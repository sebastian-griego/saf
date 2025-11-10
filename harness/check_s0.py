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

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", required=True, help="Folder with JSON items")
    ap.add_argument("--project", required=True, help="Lean Lake project folder (with mathlib)")
    ap.add_argument("--out", default=str(Path("reports") / "demo_run.json"))
    ap.add_argument("--s1", action="store_true", help="Use S1 normalization (semantic rewrites)")
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
    
    # Track C (Near-Miss) metrics
    track_c_items = []
    track_c_false_accepts = []
    track_c_correct_rejects = []

    for item in items:
        cid = item["id"]
        imports = item.get("imports", [])
        canonical = item["lean"]
        candidate = item.get("candidate", canonical)
        should_reject = item.get("should_reject", False)  # Track C flag
        nearmiss_type = item.get("nearmiss_type", None)

        if not run_lean_typecheck(project_dir, imports, candidate):
            tier = "S1" if args.s1 else "S0"
            status = "rejected"
            reason = "type_check_failed"
            
            # Track C: Type-check failure is correct rejection for near-misses
            if should_reject:
                track_c_items.append(cid)
                track_c_correct_rejects.append(cid)
            
            results.append({
                "id": cid,
                "status": status,
                "tier": tier,
                "reason": reason,
                "should_reject": should_reject,
                "nearmiss_type": nearmiss_type
            })
            counts["rejected"] += 1
            continue

        tier = "S1" if args.s1 else "S0"
        lhs = normalize_lean_prop(canonical, use_s1=args.s1)
        rhs = normalize_lean_prop(candidate, use_s1=args.s1)
        if lhs == rhs:
            status = "accepted"
            
            # Track C: Check for false accepts
            if should_reject:
                track_c_items.append(cid)
                track_c_false_accepts.append({
                    "id": cid,
                    "nearmiss_type": nearmiss_type,
                    "canonical": canonical,
                    "candidate": candidate,
                    "canonical_norm": lhs,
                    "candidate_norm": rhs
                })
            
            results.append({
                "id": cid,
                "status": status,
                "tier": tier,
                "should_reject": should_reject,
                "nearmiss_type": nearmiss_type
            })
            counts["accepted"] += 1
        else:
            status = "rejected"
            reason = "normalized_mismatch"
            
            # Track C: Correct rejection for near-misses
            if should_reject:
                track_c_items.append(cid)
                track_c_correct_rejects.append(cid)
            
            results.append({
                "id": cid,
                "status": status,
                "tier": tier,
                "reason": reason,
                "canonical_norm": lhs,
                "candidate_norm": rhs,
                "should_reject": should_reject,
                "nearmiss_type": nearmiss_type
            })
            counts["rejected"] += 1

    # Calculate Track C metrics
    track_c_summary = {}
    if track_c_items:
        total_nearmiss = len(track_c_items)
        false_accepts = len(track_c_false_accepts)
        correct_rejects = len(track_c_correct_rejects)
        fanm = false_accepts / total_nearmiss if total_nearmiss > 0 else 0.0
        
        track_c_summary = {
            "total_nearmiss": total_nearmiss,
            "false_accepts": false_accepts,
            "correct_rejects": correct_rejects,
            "fanm": fanm,  # False Accept Rate on Near-Miss
            "false_accept_details": track_c_false_accepts
        }

    summary = {
        "counts": counts,
        "total": len(items),
        "track_c": track_c_summary
    }
    out = {"summary": summary, "results": results}
    out_path.write_text(json.dumps(out, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Wrote {out_path}")
    
    # Print Track C summary if present
    if track_c_summary:
        print(f"\nTrack C (Near-Miss) Summary:")
        print(f"  Total near-miss test cases: {track_c_summary['total_nearmiss']}")
        print(f"  False accepts: {track_c_summary['false_accepts']}")
        print(f"  Correct rejects: {track_c_summary['correct_rejects']}")
        print(f"  FANM (False Accept Rate): {track_c_summary['fanm']:.2%}")
        if track_c_summary['false_accepts'] > 0:
            print(f"\n  ⚠️  WARNING: {track_c_summary['false_accepts']} near-miss variants were incorrectly accepted!")
            print(f"  Check false_accept_details in the report for details.")

if __name__ == "__main__":
    main()
