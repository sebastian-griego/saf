"""SAF V0 harness: type-check and normalize Lean propositions for fidelity testing."""
import argparse, json, subprocess, tempfile
from pathlib import Path
from normalize import normalize_lean_prop

def run_lean_typecheck(project_dir: Path, imports: list[str], candidate: str) -> bool:
    """Type-check the candidate proposition using Lean."""
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
            shell=False
        )
        return proc.returncode == 0
    finally:
        # Clean up the temporary file
        try:
            tmp_path.unlink()
        except OSError:
            pass  # Ignore errors if file was already deleted or doesn't exist

def run_lean_equiv_proof(project_dir: Path, imports: list[str], canonical: str, candidate: str, timeout: int = 5) -> bool:
    """Prove equivalence between canonical and candidate propositions using Lean (S3-Lite).
    
    Attempts to prove `canonical ↔ candidate` using Lean tactics.
    Returns True if proof succeeds within timeout, False otherwise.
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
    lines.append("def _canonical : Prop :=")
    lines.append(f"  {canonical}")
    lines.append("")
    lines.append("def _candidate : Prop :=")
    lines.append(f"  {candidate}")
    lines.append("")
    lines.append("theorem _equiv : _canonical ↔ _candidate := by")
    # Try multiple tactics in order: rfl (definitional), simp_all (simplifications), tauto (propositional)
    # If all fail, the proof will fail and we return False
    lines.append("  rfl <|> simp_all <|> tauto")
    
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
        # Check stderr for errors (Lean outputs errors to stderr)
        if proc.returncode == 0:
            # Check stderr for error messages
            if proc.stderr and ("error" in proc.stderr.lower() or "failed" in proc.stderr.lower()):
                return False
            return True
        return False
    except subprocess.TimeoutExpired:
        return False
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
    ap.add_argument("--s3-timeout", type=int, default=5, help="Timeout for S3-Lite proofs in seconds (default: 5)")
    args = ap.parse_args()

    data_dir = Path(args.data)
    project_dir = Path(args.project)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    items = []
    for p in sorted(data_dir.glob("*.json")):
        items.append(json.loads(p.read_text(encoding="utf-8")))

    results = []
    counts = {"accepted": 0, "rejected": 0}
    tier_counts = {"S0": 0, "S1": 0, "S3-Lite": 0}

    for item in items:
        cid = item["id"]
        imports = item.get("imports", [])
        canonical = item["lean"]
        candidate = item.get("candidate", canonical)

        # Step 1: Type-check the candidate
        if not run_lean_typecheck(project_dir, imports, candidate):
            tier = "S1" if args.s1 else "S0"
            results.append({
                "id": cid,
                "status": "rejected",
                "tier": tier,
                "reason": "type_check_failed"
            })
            counts["rejected"] += 1
            continue

        # Step 2: Try S0/S1 normalization
        tier = "S1" if args.s1 else "S0"
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
        if args.s3_lite:
            if run_lean_equiv_proof(project_dir, imports, canonical, candidate, timeout=args.s3_timeout):
                results.append({
                    "id": cid,
                    "status": "accepted",
                    "tier": "S3-Lite"
                })
                counts["accepted"] += 1
                tier_counts["S3-Lite"] = tier_counts.get("S3-Lite", 0) + 1
                continue

        # All checks failed - reject
        result = {
            "id": cid,
            "status": "rejected",
            "tier": tier,
            "reason": "normalized_mismatch",
            "canonical_norm": lhs,
            "candidate_norm": rhs
        }
        if args.s3_lite:
            result["s3_lite_attempted"] = True
        results.append(result)
        counts["rejected"] += 1

    summary = {
        "counts": counts,
        "total": len(items),
        "tier_breakdown": tier_counts
    }
    out = {"summary": summary, "results": results}
    out_path.write_text(json.dumps(out, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Wrote {out_path}")
    print(f"Accepted: {counts['accepted']}/{len(items)}")
    print(f"Tier breakdown: {tier_counts}")

if __name__ == "__main__":
    main()
