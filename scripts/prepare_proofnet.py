import json
import re
from pathlib import Path

def split_decl(src: str) -> tuple[str, str]:
    """
    Splits a Lean source string into:
    1. Preamble (definitions before the theorem)
    2. Proposition (the type of the theorem, without 'theorem name :' or ':=')
    """
    # Find the start of the theorem/lemma
    kw_match = re.search(r"\b(theorem|lemma|example)\b", src)
    if not kw_match:
        return "", src  # Fallback

    kw_pos = kw_match.start()
    preamble = src[:kw_pos].strip()
    decl_part = src[kw_pos:]

    # Parse the declaration header: "theorem name (binders) : Type :="
    # 1. Drop the keyword and name
    m_header = re.match(r"(?:theorem|lemma|example)\s+[^\s{[(]+\s*(.*)", decl_part, re.DOTALL)
    if not m_header:
        return preamble, decl_part

    rest = m_header.group(1).strip()
    
    # 2. Cut off the proof (text after the last :=)
    # Note: This is a heuristic. It assumes ':=' separates type and proof.
    if ":=" in rest:
        rest_no_proof = rest.rsplit(":=", 1)[0].strip()
    else:
        rest_no_proof = rest

    # 3. Split binders and type at the colon
    # We look for the *last* colon that isn't inside parentheses/brackets
    # A simple heuristic: split on the first colon if binders exist? 
    # Better: Just return the whole thing as a "forall" if it has binders.
    
    # Clean up leading binders if they exist
    # " (a : Nat) : a = a"  -> "∀ (a : Nat), a = a"
    if ":" in rest_no_proof:
        # Try to detect if we have binders before the colon
        parts = rest_no_proof.rsplit(":", 1)
        binders = parts[0].strip()
        prop = parts[1].strip()
        
        if binders:
            # Convert binders to forall
            prop = f"∀ {binders}, {prop}"
        
        return preamble, prop
    
    return preamble, rest_no_proof

def main():
    # Input file (using the one with full context)
    src_file = Path("data_proofnetverif_100/proofnetverif_valid_100.json")
    out_dir = Path("data_proofnet_ready")
    out_dir.mkdir(parents=True, exist_ok=True)

    if not src_file.exists():
        print(f"Error: {src_file} not found.")
        return

    print(f"Reading {src_file}...")
    data = json.loads(src_file.read_text(encoding="utf-8"))

    count = 0
    for item in data:
        # 1. Process Canonical (Lean)
        # Extract preamble (defs) and the pure proposition
        preamble, canonical_prop = split_decl(item["lean"])
        
        # 2. Process Candidate
        # Candidate usually comes as "theorem dummy ... := sorry", we just want the prop
        _, candidate_prop = split_decl(item["candidate"])

        # 3. Merge Preamble into Imports
        # The harness appends string imports directly to the file
        base_imports = item.get("imports", "")
        full_imports = base_imports + "\n\n" + preamble

        # 4. Create new item
        new_item = {
            "id": item["id"],
            "domain": "proofnet",
            "nl": item["nl"],
            "lean": canonical_prop,
            "candidate": candidate_prop,
            "imports": full_imports
        }

        # 5. Save individual file (sanitize ID for filename)
        safe_id = re.sub(r"[^a-zA-Z0-9_]", "_", item["id"])
        out_path = out_dir / f"{safe_id}.json"
        out_path.write_text(json.dumps(new_item, indent=2, ensure_ascii=False), encoding="utf-8")
        count += 1

    print(f"Successfully prepared {count} items in {out_dir}/")

if __name__ == "__main__":
    main()