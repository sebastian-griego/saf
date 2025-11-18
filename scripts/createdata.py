from datasets import load_dataset
from pathlib import Path
import json


def main() -> None:
    # first 100 examples from the "valid" split
    ds = load_dataset("PAug/ProofNetVerif", split="valid[:100]")

    out_dir = Path("data_proofnetverif_100")
    out_dir.mkdir(exist_ok=True)

    records = []
    for row in ds:
        rec = {
            "id": row["id"],
            "domain": "proofnetverif",
            "nl": row["nl_statement"],
            "imports": row["lean4_src_header"],
            "lean": row["lean4_formalization"],
            "candidate": row["lean4_prediction"],
            "label_equiv": bool(row["correct"]),
        }
        records.append(rec)

    out_path = out_dir / "proofnetverif_valid_100.json"
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(records, f, ensure_ascii=False, indent=2)

    print(f"wrote {len(records)} examples to {out_path}")


if __name__ == "__main__":
    main()
