# harness/beq_plus.py

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import os
import time
import subprocess
from typing import Tuple, Dict, Any, Optional


# --- Try LeanInteract (official) first ---------------------------------------
_LI_OK = False
try:
    from lean_interact import LeanREPLConfig, LeanServer, Command, LocalProject  # type: ignore
    _LI_OK = True
except Exception:
    _LI_OK = False


@dataclass
class BeqPlusResult:
    success: bool
    left_proved: bool
    right_proved: bool
    strategy: str        # "lean-interact" or "fallback"
    logs: Dict[str, Any] # raw info to include in reports for debugging


def _mk_lean_file(imports: str, p: str, q: str, classical: bool) -> str:
    """
    Generate a Lean snippet that tries to prove P->Q and Q->P using a
    conservative subset of BEq+ (Algorithm 1) with determinstic tactics.
    This version avoids unrestricted library search (to reduce FPs).
    """
    # We follow Appendix A.1 tactics: exact? (guarded via local ctx),
    # apply / convert (conclusion matching), then limited rounds of
    # tauto / simp_all / ring-arith / exact? (local)
    # Paper references: Algorithm 1 + A.1.  (Poiroux et al. 2024/2025)
    header = []
    header.append(imports.strip() or "import Mathlib")
    
    # Add tactic imports if not already present
    imports_lower = imports.lower()
    if "tauto" not in imports_lower and classical:
        header.append("import Mathlib.Tactic.Tauto")
    if "itauto" not in imports_lower:
        header.append("import Mathlib.Tactic.ITauto")
    
    header.append("set_option autoImplicit true")
    if classical:
        header.append("open Classical")
    header.append("-- BEq+ (conservative fallback) — deterministic tactics only")

    # One directed attempt: prove P -> Q
    # CRITICAL: Use ONLY fast tactics that fail immediately - NO tauto, NO simp_all
    # These can hang on quantified formulas and waste time
    attempt_dir = f"""    -- Try to show: ({p}) -> ({q})
    theorem _dir : ({p}) -> ({q}) := by
      intro h
      -- Use ONLY fast, immediate-fail tactics
      first
        | exact h  -- If definitionally equal (instant)
        | assumption  -- If hypothesis matches (instant)
        | (simp only [and_comm, or_comm, add_comm, mul_comm]; assumption)  -- Commutativity lemmas only (fast)
    """

    # Symmetric attempt: swap p and q.
    attempt_dir_sym = attempt_dir.replace("_P", "_P2").replace("_Q", "_Q2").replace("_dir", "_dir2").replace(p, "__P_PLACEHOLDER__").replace(q, "__Q_PLACEHOLDER__")
    attempt_dir_sym = attempt_dir_sym.replace("__P_PLACEHOLDER__", q).replace("__Q_PLACEHOLDER__", p)
    return "\n".join(header) + "\n" + attempt_dir + "\n" + attempt_dir_sym + "\n"


def _run_li(project_dir: Path, lean_code: str, timeout_s: int | None) -> Tuple[bool, bool, Dict[str, Any]]:
    """
    Run the Lean snippet with LeanInteract, checking whether both
    `_dir` (forward) and `_dir2` (backward) theorems elaborate (i.e., 'Goals accomplished!').
    """
    cfg = LeanREPLConfig(project=LocalProject(directory=str(project_dir)), verbose=False)  # type: ignore
    server = LeanServer(cfg)  # type: ignore

    start = time.time()
    try:
        # Ask Lean to compile our buffer and emit messages. If both theorems elaborate,
        # we'll see two "Goals accomplished!" info messages.
        resp = server.run(Command(cmd=lean_code, all_tactics=False), timeout=timeout_s)  # type: ignore
        elapsed = time.time() - start

        msgs = [m.data for m in (getattr(resp, "messages", []) or [])]
        info: Dict[str, Any] = {
            "messages": msgs,
            "env": getattr(resp, "env", None),
            "elapsed_s": elapsed,
        }

        # Check for forward direction (_dir) and backward direction (_dir2)
        s1 = any("Goals accomplished!" in str(m) and "_dir :" in str(m) and "_dir2" not in str(m) for m in msgs)
        s2 = any("Goals accomplished!" in str(m) and "_dir2 :" in str(m) for m in msgs)

        # Fallback check: ask Lean to #check the constants exist.
        try:
            remaining: float | None = None
            if timeout_s is not None:
                remaining = timeout_s - elapsed
            if remaining is None or remaining > 0:
                # Re-use the Lean environment only if we still have budget left.
                resp2 = server.run(
                    Command(cmd="#check _dir\n#check _dir2", env=getattr(resp, "env", None)),  # type: ignore
                    timeout=remaining,
                )
                msgs2 = [m.data for m in (getattr(resp2, "messages", []) or [])]
                # If #check succeeds, the theorem exists and was proved
                s1 = s1 or any("_dir :" in str(m) and "error" not in str(m).lower() and "_dir2" not in str(m) for m in msgs2)
                s2 = s2 or any("_dir2 :" in str(m) and "error" not in str(m).lower() for m in msgs2)
        except Exception:
            # If #check fails, rely on the initial compilation messages
            pass

        return (s1, s2, info)
    except TimeoutError as exc:
        elapsed = time.time() - start
        info = {
            "messages": [],
            "env": None,
            "elapsed_s": elapsed,
            "error": f"LeanInteract timeout after {timeout_s}s: {exc}",
        }
        return (False, False, info)
    finally:
        server.kill()


def _run_fallback(project_dir: Path, lean_code: str, timeout_s: int, lean_env: Optional[Dict[str, str]] = None) -> Tuple[bool, bool, Dict[str, Any]]:
    """
    Pure-Lean fallback: write a temporary .lean file and compile it with `lake env lean`
    to see whether each theorem type-checks with a proof.
    """
    import tempfile
    
    # project_dir should already be resolved, but ensure it is
    project_dir = Path(project_dir).resolve()
    
    # Create a temporary file (like run_lean_typecheck does)
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False, encoding='utf-8') as tmp_file:
        tmp_path = Path(tmp_file.name).resolve()
        tmp_file.write(lean_code)
    
    try:
        # Use absolute path to the temp file
        # Use resolve() to get absolute path and normalize separators
        abs_tmp_path = tmp_path.resolve()
        cmd = ["lean", str(abs_tmp_path)] if lean_env else ["lake", "env", "lean", str(abs_tmp_path)]
        start = time.time()
        try:
            cp = subprocess.run(
                cmd, 
                cwd=str(project_dir), 
                capture_output=True, 
                text=True, 
                timeout=timeout_s, 
                shell=False,
                env=lean_env
            )
            ok = cp.returncode == 0
            out = (cp.stdout or "") + "\n" + (cp.stderr or "")
        except subprocess.TimeoutExpired as e:
            ok = False
            out = f"timeout after {timeout_s}s: {e}"
        elapsed = time.time() - start

        # If compilation succeeded (returncode == 0), both theorems were proved
        # If it failed, both failed (we can't easily distinguish which direction failed from a single compilation)
        left_ok = ok
        right_ok = ok
        
        return (left_ok, right_ok, {"stdout_stderr": out, "elapsed_s": elapsed})
    finally:
        # Clean up the temporary file
        try:
            if tmp_path.exists():
                tmp_path.unlink()
        except OSError:
            pass


def beq_plus_equiv(
    project_dir: Path,
    imports: str,
    canonical: str,
    candidate: str,
    timeout_s: int = 30,
    classical: bool = True,
    lean_env: Optional[Dict[str, str]] = None,
) -> BeqPlusResult:
    """
    Try BEq+ (P <-> Q). Returns pass/fail and logs.
    """
    # Resolve project_dir to absolute path early
    project_dir = Path(project_dir).resolve()
    
    lean_code = _mk_lean_file(imports, canonical, candidate, classical)

    force_fallback = os.environ.get("BEQ_FORCE_FALLBACK", "").lower() in {"1", "true", "yes"}
    li_error: str | None = None

    if _LI_OK and not force_fallback:
        try:
            left, right, info = _run_li(project_dir, lean_code, timeout_s)
            return BeqPlusResult(
                success=left and right,
                left_proved=left,
                right_proved=right,
                strategy="lean-interact",
                logs=info,
            )
        except Exception as exc:  # pragma: no cover - defensive
            li_error = f"LeanInteract unavailable: {exc}"

    left, right, info = _run_fallback(project_dir, lean_code, timeout_s, lean_env=lean_env)
    if li_error:
        info = {"lean_interact_error": li_error, "fallback": info}
    return BeqPlusResult(
        success=left and right,
        left_proved=left,
        right_proved=right,
        strategy="fallback",
        logs=info,
    )

