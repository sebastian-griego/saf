"""SAF V0 harness: type-check and normalize Lean propositions for fidelity testing."""
import argparse, json, subprocess, tempfile
from pathlib import Path
from normalize import normalize_lean_prop
from run_lean_pretty_print import run_lean_pretty_print
from pretty_print_lean import STRICT_PP_OPTIONS

# Try to import lean-interact for BEq+ support
try:
    from lean_interact import beq_plus
    BEQ_PLUS_AVAILABLE = True
except ImportError:
    BEQ_PLUS_AVAILABLE = False
    beq_plus = None

def run_lean_typecheck(project_dir: Path, imports: list[str], candidate: str, timeout: int = None) -> tuple[bool, str]:
    """Type-check the candidate proposition using Lean.
    
    Returns:
        Tuple of (success: bool, stderr: str)
    """
    lines = []
    import_map = {
        "Mathlib.Algebra.Divisibility": "Mathlib.Algebra.Divisibility.Basic"
    }
    for imp in imports:
        normalized_imp = imp.replace("/", ".")
        normalized_imp = import_map.get(normalized_imp, normalized_imp)
        lines.append(f"import {normalized_imp}")
    lines.append("")
    lines.append("def _candidate : Prop :=")
    lines.append(f"  {candidate}")
    lines.append("")
    lines.append("#check (_candidate : Prop)")
    
    # Use a temporary file for Check.lean
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False, encoding='utf-8') as tmp_file:
        tmp_path = Path(tmp_file.name)
        tmp_file.write("\n".join(lines))
    
    try:
        # Use absolute path to the temp file
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp_path)],
            cwd=str(project_dir),
            capture_output=True,
            text=True,
            shell=False,
            timeout=timeout
        )
        return (proc.returncode == 0, proc.stderr or "")
    except subprocess.TimeoutExpired:
        return (False, "Type-check timeout expired")
    finally:
        # Clean up the temporary file
        try:
            tmp_path.unlink()
        except OSError:
            pass  # Ignore errors if file was already deleted or doesn't exist

def run_lean_equiv_proof(project_dir: Path, imports: list[str], canonical: str, candidate: str, timeout: int = 5, s3_lite: bool = False, use_classical: bool = False) -> tuple[bool, str]:
    """Prove equivalence between canonical and candidate propositions using Lean (S3-Lite).
    
    Uses a logic-only equivalence tier with lean-native decision procedures:
    1. rfl (definitional equality)
    2. simp only (logic whitelist: De Morgan, quantifier negation, assoc/comm of ∧/∨, etc.)
    3. itauto (intuitionistic tautology prover)
    4. tauto (classical tautology prover, optional, off by default)
    
    This ensures deterministic "logic-only" equivalence without pulling in domain facts.
    
    Args:
        project_dir: Path to Lean project directory
        imports: List of imports for the proof
        canonical: Canonical proposition
        candidate: Candidate proposition
        timeout: Timeout in seconds
        s3_lite: If True, use logic-only equivalence tier (rfl → simp only → itauto → optional tauto)
        use_classical: If True, include tauto (classical reasoning) in the proof chain. 
                      Only used when s3_lite is True. Off by default.
    
    Returns:
        Tuple of (success: bool, stderr: str)
    """
    lines = []
    import_map = {
        "Mathlib.Algebra.Divisibility": "Mathlib.Algebra.Divisibility.Basic"
    }
    for imp in imports:
        normalized_imp = imp.replace("/", ".")
        normalized_imp = import_map.get(normalized_imp, normalized_imp)
        lines.append(f"import {normalized_imp}")
    
    # Add imports for logic tactics if using S3-Lite
    if s3_lite:
        # Normalize imports for comparison
        normalized_imports = [imp.replace("/", ".") for imp in imports]
        normalized_imports = [import_map.get(imp, imp) for imp in normalized_imports]
        
        # Ensure we have the logic tactics available
        # These might already be imported via Mathlib, but we make sure
        if "Mathlib.Tactic.ITauto" not in normalized_imports:
            lines.append("import Mathlib.Tactic.ITauto")
        if use_classical and "Mathlib.Tactic.Tauto" not in normalized_imports:
            lines.append("import Mathlib.Tactic.Tauto")
        # Ensure we have logic lemmas (needed for not_forall, not_exists, etc.)
        if "Mathlib.Logic.Basic" not in normalized_imports:
            lines.append("import Mathlib.Logic.Basic")
    
    lines.append("")
    lines.append("def _canonical : Prop :=")
    lines.append(f"  {canonical}")
    lines.append("")
    lines.append("def _candidate : Prop :=")
    lines.append(f"  {candidate}")
    lines.append("")
    lines.append("theorem _equiv : _canonical ↔ _candidate := by")
    
    if s3_lite:
        # Logic-only equivalence tier: rfl → simp only → itauto → optional tauto
        # This gives deterministic "logic-only" equivalence without domain facts
        
        # Logic whitelist for simp only:
        # - De Morgan: not_and_or, not_or
        # - Quantifier negation: not_forall, not_exists  
        # - Associativity: and_assoc, or_assoc
        # - Commutativity: and_comm, or_comm
        # - Inequality: not_ne_iff (for x ≠ y ↔ ¬ x = y, though ≠ is definitional)
        # - Iff simplification: iff_true, iff_false
        # - Implication: imp_true, true_imp
        logic_whitelist = [
            "not_and_or",      # De Morgan: ¬(a ∧ b) ↔ ¬a ∨ ¬b
            "not_or",          # De Morgan: ¬(a ∨ b) ↔ ¬a ∧ ¬b
            "not_forall",      # Quantifier negation: ¬∀x, P x ↔ ∃x, ¬P x
            "not_exists",      # Quantifier negation: ¬∃x, P x ↔ ∀x, ¬P x
            "and_assoc",       # Associativity: (a ∧ b) ∧ c ↔ a ∧ b ∧ c
            "or_assoc",        # Associativity: (a ∨ b) ∨ c ↔ a ∨ b ∨ c
            "and_comm",        # Commutativity: a ∧ b ↔ b ∧ a
            "or_comm",         # Commutativity: a ∨ b ↔ b ∨ a
            "not_ne_iff",      # Inequality: ¬a ≠ b ↔ a = b
            "iff_true",        # Iff simplification
            "iff_false",       # Iff simplification
            "imp_true",        # Implication simplification
            "true_imp",        # Implication simplification
        ]
        logic_whitelist_str = ", ".join(logic_whitelist)
        
        # Use first tactic that succeeds (left to right)
        lines.append("  first")
        lines.append("  | rfl")  # Step 1: Definitional equality
        lines.append(f"  | simp only [{logic_whitelist_str}]")  # Step 2: Logic-only simplification
        lines.append("  | itauto")  # Step 3: Intuitionistic tautology prover
        
        # Step 4: Classical tautology prover (optional, off by default)
        if use_classical:
            lines.append("  | tauto")
    else:
        # Legacy mode: use full simp_all and constructor-based proofs
        lines.append("  first")
        lines.append("  | rfl")
        lines.append("  | simp_all")
        lines.append("  | (constructor; (intro; (simp_all <|> assumption)))")
        # Classical reasoning (contraposition) is opt-in
        if use_classical:
            lines.append("  | (classical; constructor; (intro; (contrapose!; assumption)))")
    
    # Use a temporary file for the proof
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False, encoding='utf-8') as tmp_file:
        tmp_path = Path(tmp_file.name)
        tmp_file.write("\n".join(lines))
    
    try:
        # Run with timeout
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp_path)],
            cwd=str(project_dir),
            capture_output=True,
            text=True,
            shell=False,
            timeout=timeout
        )
        # If Lean compiles successfully (returncode == 0), the proof succeeded
        # Lean will not compile if there are errors, so returncode == 0 means success
        return (proc.returncode == 0, proc.stderr or "")
    except subprocess.TimeoutExpired:
        return (False, "Proof timeout expired")
    finally:
        # Clean up the temporary file
        try:
            tmp_path.unlink()
        except OSError:
            pass  # Ignore errors if file was already deleted or doesn't exist

def run_beq_plus_check(project_dir: Path, imports: list[str], canonical: str, candidate: str, timeout: int = 30) -> tuple[bool, str]:
    """Check statement equivalence using BEq+ metric.
    
    BEq+ proves each direction (P → Q and Q → P) with a deterministic bundle of tactics.
    This is a "heavy" tier that can catch equivalences missed by normalization.
    
    Reference: "Reliable Evaluation and Benchmarks for Statement Autoformalization" (EMNLP 2025)
    Paper: https://aclanthology.org/2025.emnlp-main.907.pdf
    Code: https://github.com/augustepoiroux/LeanInteract
    
    NOTE: This is a placeholder implementation. The actual BEq+ implementation from LeanInteract
    should be used when available. This fallback implements a simplified version based on the
    paper's description: BEq+ is deterministic, proves both directions separately, and uses
    a bundle of tactics that run efficiently on CPU without requiring large language models.
    
    Args:
        project_dir: Path to Lean project directory
        imports: List of imports for the proof
        canonical: Canonical proposition
        candidate: Candidate proposition
        timeout: Timeout in seconds (default: 30)
    
    Returns:
        Tuple of (success: bool, error_message: str)
    """
    # Try to use lean-interact package if available
    # TODO: Verify the actual API from https://github.com/augustepoiroux/LeanInteract
    # The actual BEq+ implementation may have a different interface
    if BEQ_PLUS_AVAILABLE and beq_plus is not None:
        try:
            # Attempt to use the official BEq+ implementation from LeanInteract
            # Note: This API call is a placeholder - the actual API may differ
            # Check https://github.com/augustepoiroux/LeanInteract for the correct usage
            if hasattr(beq_plus, 'check_equivalence'):
                result = beq_plus.check_equivalence(
                    canonical,
                    candidate,
                    imports=imports,
                    project_dir=str(project_dir),
                    timeout=timeout
                )
                return (result.success, result.error_message if hasattr(result, 'error_message') else "")
            elif hasattr(beq_plus, 'beq_plus'):
                # Alternative API name
                result = beq_plus.beq_plus(
                    canonical,
                    candidate,
                    imports=imports,
                    project_dir=str(project_dir),
                    timeout=timeout
                )
                return (result.success, result.error_message if hasattr(result, 'error_message') else "")
        except Exception as e:
            # If lean-interact API fails, fall back to direct Lean implementation
            # Log the error for debugging
            import sys
            print(f"Warning: lean-interact BEq+ API failed: {e}", file=sys.stderr)
            print("Falling back to direct Lean implementation.", file=sys.stderr)
    
    # Fallback: Simplified BEq+ implementation using Lean directly
    # Based on paper description: BEq+ proves both directions with deterministic tactics
    # This is a simplified approximation - the actual BEq+ may use a more sophisticated
    # tactic bundle. See the paper and LeanInteract repository for the official implementation.
    #
    # The paper states BEq+ is:
    # - Deterministic
    # - Runs efficiently on CPU
    # - Does not require a 20B LLM prover
    # - Proves P → Q and Q → P separately
    # - Correlates strongly with human judgment
    lines = []
    import_map = {
        "Mathlib.Algebra.Divisibility": "Mathlib.Algebra.Divisibility.Basic"
    }
    for imp in imports:
        normalized_imp = imp.replace("/", ".")
        normalized_imp = import_map.get(normalized_imp, normalized_imp)
        lines.append(f"import {normalized_imp}")
    lines.append("")
    lines.append("def _canonical : Prop :=")
    lines.append(f"  {canonical}")
    lines.append("")
    lines.append("def _candidate : Prop :=")
    lines.append(f"  {candidate}")
    lines.append("")
    # BEq+ proves both directions: canonical → candidate and candidate → canonical
    # Using a deterministic bundle of tactics
    # TODO: Align with actual BEq+ implementation from LeanInteract
    # The actual implementation may use a more sophisticated tactic sequence
    lines.append("theorem _beq_plus_forward : _canonical → _candidate := by")
    lines.append("  -- BEq+ deterministic tactic bundle for forward direction")
    lines.append("  -- TODO: Replace with actual BEq+ tactic bundle from LeanInteract")
    lines.append("  intro h")
    lines.append("  first")
    lines.append("  | rfl  -- Definitional equality")
    lines.append("  | assumption  -- Use hypothesis")
    lines.append("  | simp_all  -- Simplification (may be too permissive - actual BEq+ may restrict this)")
    lines.append("")
    lines.append("theorem _beq_plus_backward : _candidate → _canonical := by")
    lines.append("  -- BEq+ deterministic tactic bundle for backward direction")
    lines.append("  -- TODO: Replace with actual BEq+ tactic bundle from LeanInteract")
    lines.append("  intro h")
    lines.append("  first")
    lines.append("  | rfl  -- Definitional equality")
    lines.append("  | assumption  -- Use hypothesis")
    lines.append("  | simp_all  -- Simplification (may be too permissive - actual BEq+ may restrict this)")
    lines.append("")
    # Combine both directions to show equivalence
    lines.append("theorem _beq_plus_equiv : _canonical ↔ _candidate := by")
    lines.append("  constructor")
    lines.append("  · exact _beq_plus_forward")
    lines.append("  · exact _beq_plus_backward")
    
    # Use a temporary file for the proof
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False, encoding='utf-8') as tmp_file:
        tmp_path = Path(tmp_file.name)
        tmp_file.write("\n".join(lines))
    
    try:
        # Run with timeout
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp_path)],
            cwd=str(project_dir),
            capture_output=True,
            text=True,
            shell=False,
            timeout=timeout
        )
        # If Lean compiles successfully (returncode == 0), BEq+ succeeded
        return (proc.returncode == 0, proc.stderr or "")
    except subprocess.TimeoutExpired:
        return (False, "BEq+ timeout expired")
    finally:
        # Clean up the temporary file
        try:
            tmp_path.unlink()
        except OSError:
            pass  # Ignore errors if file was already deleted or doesn't exist

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", required=True, help="Folder with JSON items")
    ap.add_argument("--project", required=True, help="Lean Lake project folder (with mathlib)")
    ap.add_argument("--out", default=str(Path("reports") / "demo_run.json"))
    ap.add_argument("--s1", action="store_true", help="Use S1 normalization (semantic rewrites)")
    ap.add_argument("--s3-lite", action="store_true", help="Enable S3-Lite: prove equivalence if S0/S1 fails")
    ap.add_argument("--s3-classical", action="store_true", help="Enable classical reasoning (contraposition) in S3-Lite proofs")
    ap.add_argument("--strict-pp", action="store_true", help="Use Lean's pretty-printer with strict PP options for deterministic output (for strict tier)")
    ap.add_argument("--beq-plus", action="store_true", help="Enable BEq+ metric: heavy-tier equivalence checking using deterministic tactics (optional)")
    ap.add_argument("--typecheck-timeout", type=int, default=None, help="Timeout for type-checking in seconds (default: no timeout)")
    ap.add_argument("--s3-timeout", type=int, default=5, help="Timeout for S3-Lite proofs in seconds (default: 5)")
    ap.add_argument("--beq-plus-timeout", type=int, default=30, help="Timeout for BEq+ proofs in seconds (default: 30)")
    ap.add_argument("--max-tactic-steps", type=int, default=None, help="Maximum tactic steps (for documentation/auditing; not directly enforced by Lean)")
    args = ap.parse_args()
    
    # Check if BEq+ is requested but not available
    if args.beq_plus and not BEQ_PLUS_AVAILABLE:
        print("Warning: --beq-plus requested but lean-interact package not found.")
        print("Install it with: pip install lean-interact")
        print("Falling back to direct Lean implementation of BEq+.")
        print("")

    data_dir = Path(args.data)
    project_dir = Path(args.project)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    items = []
    for p in sorted(data_dir.glob("*.json")):
        items.append(json.loads(p.read_text(encoding="utf-8")))

    results = []
    counts = {"accepted": 0, "rejected": 0}
    tier_counts = {"S0": 0, "S1": 0, "S3-Lite": 0, "BEq+": 0}

    for item in items:
        cid = item["id"]
        imports = item.get("imports", [])
        canonical = item["lean"]
        candidate = item.get("candidate", canonical)

        # Step 1: Type-check the candidate
        typecheck_success, typecheck_stderr = run_lean_typecheck(project_dir, imports, candidate, timeout=args.typecheck_timeout)
        if not typecheck_success:
            tier = "S1" if args.s1 else "S0"
            result = {
                "id": cid,
                "status": "rejected",
                "tier": tier,
                "reason": "type_check_failed"
            }
            if typecheck_stderr:
                result["stderr"] = typecheck_stderr
            results.append(result)
            counts["rejected"] += 1
            continue

        # Step 2: Try S0/S1 normalization or strict PP
        tier = "S1" if args.s1 else "S0"
        
        if args.strict_pp:
            # Use Lean's pretty-printer with strict PP options
            canonical_success, lhs, canonical_stderr = run_lean_pretty_print(
                project_dir, imports, canonical, timeout=args.typecheck_timeout
            )
            candidate_success, rhs, candidate_stderr = run_lean_pretty_print(
                project_dir, imports, candidate, timeout=args.typecheck_timeout
            )
            
            if not canonical_success or not candidate_success:
                result = {
                    "id": cid,
                    "status": "rejected",
                    "tier": tier,
                    "reason": "pretty_print_failed"
                }
                if not canonical_success:
                    result["canonical_pretty_print_error"] = canonical_stderr
                if not candidate_success:
                    result["candidate_pretty_print_error"] = candidate_stderr
                results.append(result)
                counts["rejected"] += 1
                continue
        else:
            # Use Python normalization (S0/S1)
            lhs = normalize_lean_prop(canonical, use_s1=args.s1)
            rhs = normalize_lean_prop(candidate, use_s1=args.s1)
        
        if lhs == rhs:
            results.append({
                "id": cid,
                "status": "accepted",
                "tier": tier
            })
            counts["accepted"] += 1
            tier_counts[tier] = tier_counts.get(tier, 0) + 1
            continue

        # Step 3: If S0/S1 failed and S3-Lite is enabled, try proving equivalence
        proof_success = None
        proof_stderr = None
        if args.s3_lite:
            proof_success, proof_stderr = run_lean_equiv_proof(project_dir, imports, canonical, candidate, timeout=args.s3_timeout, s3_lite=True, use_classical=args.s3_classical)
            if proof_success:
                result = {
                    "id": cid,
                    "status": "accepted",
                    "tier": "S3-Lite",
                    "s3_lite_classical": args.s3_classical
                }
                if proof_stderr:
                    result["stderr"] = proof_stderr
                results.append(result)
                counts["accepted"] += 1
                tier_counts["S3-Lite"] = tier_counts.get("S3-Lite", 0) + 1
                continue

        # Step 4: If S0/S1/S3-Lite failed and BEq+ is enabled, try BEq+ metric
        beq_plus_success = None
        beq_plus_stderr = None
        if args.beq_plus:
            beq_plus_success, beq_plus_stderr = run_beq_plus_check(project_dir, imports, canonical, candidate, timeout=args.beq_plus_timeout)
            if beq_plus_success:
                result = {
                    "id": cid,
                    "status": "accepted",
                    "tier": "BEq+"
                }
                if beq_plus_stderr:
                    result["stderr"] = beq_plus_stderr
                results.append(result)
                counts["accepted"] += 1
                tier_counts["BEq+"] = tier_counts.get("BEq+", 0) + 1
                continue

        # All checks failed - reject
        result = {
            "id": cid,
            "status": "rejected",
            "tier": tier,
            "reason": "normalized_mismatch",
        }
        if args.strict_pp:
            result["canonical_pp"] = lhs
            result["candidate_pp"] = rhs
        else:
            result["canonical_norm"] = lhs
            result["candidate_norm"] = rhs
        if args.s3_lite:
            result["s3_lite_attempted"] = True
            result["s3_lite_classical"] = args.s3_classical
            # Include stderr from failed proof attempt if available
            if not proof_success and proof_stderr:
                result["stderr"] = proof_stderr
        if args.beq_plus:
            result["beq_plus_attempted"] = True
            # Include stderr from failed BEq+ attempt if available
            if not beq_plus_success and beq_plus_stderr:
                result["beq_plus_stderr"] = beq_plus_stderr
        results.append(result)
        counts["rejected"] += 1

    # Build proof budget metadata for auditability
    proof_budget = {
        "typecheck_timeout_seconds": args.typecheck_timeout,
        "s3_timeout_seconds": args.s3_timeout if args.s3_lite else None,
        "beq_plus_timeout_seconds": args.beq_plus_timeout if args.beq_plus else None,
        "max_tactic_steps": args.max_tactic_steps,
        "beq_plus_available": BEQ_PLUS_AVAILABLE
    }
    
    # Build run manifest with PP options if using strict PP
    run_manifest = {}
    if args.strict_pp:
        run_manifest["pretty_printer"] = {
            "method": "lean_delaborator",
            "options": STRICT_PP_OPTIONS.copy()
        }

    summary = {
        "counts": counts,
        "total": len(items),
        "tier_breakdown": tier_counts,
        "proof_budget": proof_budget
    }
    if run_manifest:
        summary["run_manifest"] = run_manifest
    out = {"summary": summary, "results": results}
    out_path.write_text(json.dumps(out, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Wrote {out_path}")
    print(f"Accepted: {counts['accepted']}/{len(items)}")
    print(f"Tier breakdown: {tier_counts}")

if __name__ == "__main__":
    main()
