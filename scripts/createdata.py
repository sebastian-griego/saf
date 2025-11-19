from pathlib import Path
import json
import re

from datasets import load_dataset


def theorem_to_prop(src: str) -> str:
    """Convert a full theorem/lemma/example declaration to a Prop string.

    Handles things of the form:

      /-- doc comment -/
      theorem name {binders} : Type := proof

    Returns something like:

      "∀ {binders}, Type"

    If parsing fails we just return the original string.
    """
    text = src.strip()

    # Drop leading doc comment if present
    kw_pos = None
    for kw in ("theorem", "lemma", "example"):
        i = text.find(kw)
        if i != -1 and (kw_pos is None or i < kw_pos):
            kw_pos = i
    if kw_pos is None:
        # Nothing to do
        return text

    header = text[kw_pos:]

    m = re.match(r"(theorem|lemma|example)\s+([^\s:]+)\s*(.*)", header, re.DOTALL)
    if not m:
        return text

    rest = m.group(3).strip()

    # Cut off the proof part
    rest_no_proof = rest.split(":=", 1)[0].strip()

    # Split at the last ":" to separate binders and result type
    if ":" not in rest_no_proof:
        # Already just a Prop, nothing to do
        return rest_no_proof

    binders_part, type_part = rest_no_proof.rsplit(":", 1)
    binders_part = binders_part.strip()
    type_part = type_part.strip()

    if not type_part:
        return rest_no_proof

    if binders_part:
        # This binder syntax is valid after "∀"
        return f"∀ {binders_part}, {type_part}"
    else:
        return type_part


def main():
    out_dir = Path("data_proofnetverif")
    out_dir.mkdir(exist_ok=True)

    # First 100 from the "valid" split
    ds = load_dataset("PAug/ProofNetVerif", split="valid[:100]")

    records = []
    for ex in ds:
        lean_form = ex["lean4_formalization"]
        lean_pred = ex["lean4_prediction"]

        lean_prop = theorem_to_prop(lean_form)
        cand_prop = theorem_to_prop(lean_pred)

        records.append(
            {
                "id": ex["id"],
                "nl": ex["nl_statement"],
                "imports": ex["lean4_src_header"],
                "lean": lean_prop,
                "candidate": cand_prop,
                "label_correct": bool(ex["correct"]),
            }
        )

    out_path = out_dir / "first100.json"
    with out_path.open("w", encoding="utf8") as f:
        json.dump(records, f, ensure_ascii=False, indent=2)

    print("wrote", len(records), "examples to", out_path)


if __name__ == "__main__":
    main()
