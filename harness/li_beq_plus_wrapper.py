"""Thin wrapper around LeanInteract's BEq+ implementation.

This isolates all LeanInteract wiring (project discovery, REPL config, etc.)
so the rest of the SAF harness can just call `run_beq_plus`.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Optional

try:  # LeanInteract is optional for most SAF workflows
    from lean_interact import LeanREPLConfig, LocalProject  # type: ignore
except Exception:  # pragma: no cover - dependency missing at runtime
    LeanREPLConfig = None  # type: ignore
    LocalProject = None  # type: ignore

li_beq = None  # type: ignore
try:
    from third_party import leaninteract_beq_plus as li_beq  # type: ignore
except Exception:  # pragma: no cover - module search path might not include harness
    try:
        from harness.third_party import leaninteract_beq_plus as li_beq  # type: ignore
    except Exception:
        li_beq = None  # type: ignore

# Keep the cache near the drive root on Windows to avoid MAX_PATH issues
CACHE_DIR = Path("C:/Temp/li_cache") if os.name == "nt" else Path(__file__).parent / ".lean_interact_cache"
CACHE_DIR.mkdir(exist_ok=True, parents=True)


def _wrap_prop_as_theorem(name: str, proposition: str) -> str:
    """Convert a proposition string into a Lean theorem declaration."""
    return f"theorem {name} : {proposition.strip()} := by sorry"


def make_lean_project_config(project_dir: Path, timeout_seconds: Optional[int] = 30):
    """Create the LeanInteract REPL config backed by the SAF Lean project."""
    if LeanREPLConfig is None or LocalProject is None:
        raise RuntimeError(
            "lean-interact is not installed; install it (pip install lean-interact) "
            "to use the BEq+ metric."
        )
    project = LocalProject(directory=str(Path(project_dir).resolve()))
    # LeanInteract exposes timeouts via the server invocation, so we just stash the
    # budget inside the config for convenience.
    config = LeanREPLConfig(  # type: ignore[arg-type]
        project=project,
        cache_dir=str(CACHE_DIR.resolve()),
        enable_incremental_optimization=False,
        enable_parallel_elaboration=False,
        verbose=False,
    )
    if timeout_seconds is not None and hasattr(config, "timeout"):
        setattr(config, "timeout", timeout_seconds)
    return config


def run_beq_plus(
    project_dir: Path,
    stmt_ref: str,
    stmt_cand: str,
    header: str,
    timeout_seconds: int = 30,
    verbose: bool = False,
) -> bool:
    """Execute LeanInteract's BEq+ metric on two Lean theorem statements."""
    if li_beq is None:
        raise RuntimeError(
            "Missing vendored LeanInteract BEq+ script. Ensure "
            "`harness/third_party/leaninteract_beq_plus.py` exists."
        )
    config = make_lean_project_config(project_dir, timeout_seconds=timeout_seconds)
    src_header = header.strip() or "import Mathlib"
    canonical_thm = _wrap_prop_as_theorem("_beq_reference", stmt_ref)
    candidate_thm = _wrap_prop_as_theorem("_beq_candidate", stmt_cand)
    return bool(
        li_beq.beq_plus(
            canonical_thm,
            candidate_thm,
            src_header,
            config,
            timeout_per_proof=timeout_seconds,
            verbose=verbose,
        )
    )


__all__ = ["run_beq_plus", "make_lean_project_config"]
