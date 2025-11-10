"""SAF V0 harness: type-check and normalize Lean propositions for fidelity testing."""
import argparse, json, subprocess
from pathlib import Path
from normalize import normalize_lean_prop

def run_lean_typecheck(project_dir: Path, imports: list[str], candidate: str) -> bool:
    """Type-check the candidate proposition using Lean."""
    check_file = project_dir / "Check.lean"
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
    check_file.write_text("\n".join(lines), encoding="utf-8")

    proc = subprocess.run(
        ["lake", "env", "lean", "Check.lean"],
        cwd=str(project_dir),
        capture_output=True,
        text=True,
        shell=True
    )
    return proc.returncode == 0

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

    for item in items:
        cid = item["id"]
        imports = item.get("imports", [])
        canonical = item["lean"]
        candidate = item.get("candidate", canonical)

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
        else:
            results.append({
                "id": cid,
                "status": "rejected",
                "tier": tier,
                "reason": "normalized_mismatch",
                "canonical_norm": lhs,
                "candidate_norm": rhs
            })
            counts["rejected"] += 1

    summary = {"counts": counts, "total": len(items)}
    out = {"summary": summary, "results": results}
    out_path.write_text(json.dumps(out, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Wrote {out_path}")

if __name__ == "__main__":
    main()
