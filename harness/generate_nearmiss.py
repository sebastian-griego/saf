"""Generate adversarial near-miss variants for Track C testing.

Near-miss variants are minimally wrong Lean statements that should be rejected
by the benchmark (non-equivalent to canonical).
"""
import json
import re
from pathlib import Path
from typing import Dict, List, Tuple


def generate_operator_swaps(lean: str) -> List[Tuple[str, str]]:
    """Generate variants by swapping operators.
    
    Returns: List of (variant_lean, description) tuples.
    """
    variants = []
    
    # ≤ ↔ <
    if "≤" in lean:
        variant = lean.replace("≤", "<")
        variants.append((variant, "operator_swap_le_to_lt"))
    if "<" in lean:
        variant = lean.replace("<", "≤")
        variants.append((variant, "operator_swap_lt_to_le"))
    
    # ≥ ↔ >
    if "≥" in lean:
        variant = lean.replace("≥", ">")
        variants.append((variant, "operator_swap_ge_to_gt"))
    if ">" in lean:
        variant = lean.replace(">", "≥")
        variants.append((variant, "operator_swap_gt_to_ge"))
    
    # = ↔ ≠
    if "=" in lean and "≠" not in lean:
        # Replace = with ≠, but be careful not to replace in binders like "a : ℕ"
        # Simple heuristic: replace " = " (with spaces) to avoid binders
        variant = re.sub(r'\s+=\s+', ' ≠ ', lean)
        variants.append((variant, "operator_swap_eq_to_neq"))
    
    return variants


def generate_quantifier_swaps(lean: str) -> List[Tuple[str, str]]:
    """Generate variants by swapping quantifiers.
    
    Returns: List of (variant_lean, description) tuples.
    """
    variants = []
    
    # ∀ ↔ ∃
    if "∀" in lean:
        variant = lean.replace("∀", "∃")
        variants.append((variant, "quantifier_swap_forall_to_exists"))
    if "∃" in lean:
        variant = lean.replace("∃", "∀")
        variants.append((variant, "quantifier_swap_exists_to_forall"))
    
    return variants


def generate_type_swaps(lean: str) -> List[Tuple[str, str]]:
    """Generate variants by swapping types.
    
    Returns: List of (variant_lean, description) tuples.
    """
    variants = []
    
    # ℕ ↔ ℤ
    if "ℕ" in lean:
        variant = lean.replace("ℕ", "ℤ")
        variants.append((variant, "type_swap_nat_to_int"))
    if "ℤ" in lean:
        variant = lean.replace("ℤ", "ℕ")
        variants.append((variant, "type_swap_int_to_nat"))
    
    # ℕ ↔ ℝ (if ℝ is available)
    if "ℕ" in lean:
        variant = lean.replace("ℕ", "ℝ")
        variants.append((variant, "type_swap_nat_to_real"))
    
    return variants


def generate_sign_flips(lean: str) -> List[Tuple[str, str]]:
    """Generate variants by flipping arithmetic signs.
    
    Returns: List of (variant_lean, description) tuples.
    """
    variants = []
    
    # + ↔ -
    if " + " in lean:
        variant = lean.replace(" + ", " - ")
        variants.append((variant, "sign_flip_plus_to_minus"))
    if " - " in lean:
        variant = lean.replace(" - ", " + ")
        variants.append((variant, "sign_flip_minus_to_plus"))
    
    return variants


def generate_binder_swaps(lean: str) -> List[Tuple[str, str]]:
    """Generate variants by swapping variable order in binders.
    
    Example: ∀ a b : ℕ, P → ∀ b a : ℕ, P
    
    Returns: List of (variant_lean, description) tuples.
    """
    variants = []
    
    # Match patterns like "∀ a b : T, P" and swap to "∀ b a : T, P"
    pattern = r'(∀|∃)\s*\(?([a-z_]+)\s+([a-z_]+)\s*:\s*([^,)]+)\)?\s*,'
    
    def swap_vars(match):
        quant = match.group(1)
        var1 = match.group(2)
        var2 = match.group(3)
        typ = match.group(4)
        return f"{quant} ({var2} {var1} : {typ}),"
    
    variant = re.sub(pattern, swap_vars, lean)
    if variant != lean:
        variants.append((variant, "binder_swap_variable_order"))
    
    return variants


def generate_condition_drops(lean: str) -> List[Tuple[str, str]]:
    """Generate variants by dropping conditions (e.g., x ≠ 0).
    
    Returns: List of (variant_lean, description) tuples.
    """
    variants = []
    
    # Drop "x ≠ 0" type constraints
    # This is more complex - would need to parse the structure
    # For now, simple heuristic: remove "≠ 0" patterns
    if "≠ 0" in lean:
        variant = re.sub(r'\s*≠\s*0\s*', ' ', lean)
        variants.append((variant, "condition_drop_neq_zero"))
    
    return variants


def generate_nearmiss_variants(canonical_lean: str) -> List[Tuple[str, str]]:
    """Generate all near-miss variants for a canonical Lean statement.
    
    Args:
        canonical_lean: The canonical Lean statement
        
    Returns:
        List of (variant_lean, variant_type) tuples
    """
    variants = []
    
    # Apply all generators
    variants.extend(generate_operator_swaps(canonical_lean))
    variants.extend(generate_quantifier_swaps(canonical_lean))
    variants.extend(generate_type_swaps(canonical_lean))
    variants.extend(generate_sign_flips(canonical_lean))
    variants.extend(generate_binder_swaps(canonical_lean))
    variants.extend(generate_condition_drops(canonical_lean))
    
    # Remove duplicates (same variant, different generators)
    seen = set()
    unique_variants = []
    for variant, desc in variants:
        if variant != canonical_lean and variant not in seen:
            seen.add(variant)
            unique_variants.append((variant, desc))
    
    return unique_variants


def lean_to_nl_template(lean: str) -> str:
    """Convert Lean statement to NL using simple templates.
    
    This is a basic template-based back-translation for near-miss variants.
    For production, you'd want more sophisticated templates.
    """
    nl = lean
    
    # Replace quantifiers
    nl = re.sub(r'∀\s*\(?([a-z_]+)\s*:\s*ℕ\)?\s*,', r'For all natural numbers \1,', nl)
    nl = re.sub(r'∀\s*\(?([a-z_]+)\s*:\s*ℤ\)?\s*,', r'For all integers \1,', nl)
    nl = re.sub(r'∀\s*\(?([a-z_]+)\s*:\s*ℝ\)?\s*,', r'For all real numbers \1,', nl)
    nl = re.sub(r'∃\s*\(?([a-z_]+)\s*:\s*ℕ\)?\s*,', r'there exists a natural number \1 such that', nl)
    nl = re.sub(r'∃\s*([a-z_]+)\s*,', r'there exists \1 such that', nl)
    
    # Replace operators
    nl = nl.replace(" ≤ ", " is less than or equal to ")
    nl = nl.replace(" ≥ ", " is greater than or equal to ")
    nl = nl.replace(" < ", " is less than ")
    nl = nl.replace(" > ", " is greater than ")
    nl = nl.replace(" = ", " equals ")
    nl = nl.replace(" ≠ ", " does not equal ")
    nl = nl.replace(" → ", " then ")
    nl = nl.replace(" ↔ ", " if and only if ")
    nl = nl.replace(" ∧ ", " and ")
    nl = nl.replace(" ∨ ", " or ")
    nl = nl.replace("¬", "not ")
    
    # Replace arithmetic
    nl = nl.replace(" + ", " plus ")
    nl = nl.replace(" - ", " minus ")
    nl = nl.replace(" * ", " times ")
    
    # Clean up
    nl = re.sub(r'\s+', ' ', nl)
    nl = nl.strip()
    
    return nl


def create_nearmiss_test_case(
    base_id: str,
    base_item: Dict,
    variant_lean: str,
    variant_type: str,
    variant_index: int
) -> Dict:
    """Create a near-miss test case from a base test case.
    
    Args:
        base_id: Original test case ID
        base_item: Original test case JSON
        variant_lean: The near-miss Lean variant
        variant_type: Type of variant (e.g., "operator_swap_le_to_lt")
        variant_index: Index of this variant (for unique ID)
        
    Returns:
        New test case JSON dict
    """
    # Generate NL from variant (template-based)
    variant_nl = lean_to_nl_template(variant_lean)
    
    # Create new ID
    new_id = f"{base_id}_nearmiss_{variant_index:02d}_{variant_type}"
    
    return {
        "id": new_id,
        "domain": base_item.get("domain", "unknown"),
        "nl": variant_nl,
        "lean": base_item["lean"],  # Canonical (ground truth)
        "candidate": variant_lean,  # The near-miss variant
        "imports": base_item["imports"],
        "should_reject": True,  # Track C flag
        "nearmiss_type": variant_type,
        "base_id": base_id
    }


def generate_nearmiss_from_file(base_file: Path, output_dir: Path):
    """Generate near-miss test cases from a base test case file.
    
    Args:
        base_file: Path to base test case JSON
        output_dir: Directory to write near-miss test cases
    """
    base_item = json.loads(base_file.read_text(encoding="utf-8"))
    canonical_lean = base_item["lean"]
    
    # Generate variants
    variants = generate_nearmiss_variants(canonical_lean)
    
    if not variants:
        print(f"No variants generated for {base_file.name}")
        return
    
    # Create test cases for each variant
    output_dir.mkdir(parents=True, exist_ok=True)
    
    for idx, (variant_lean, variant_type) in enumerate(variants):
        test_case = create_nearmiss_test_case(
            base_item["id"],
            base_item,
            variant_lean,
            variant_type,
            idx
        )
        
        # Write to file
        output_file = output_dir / f"{test_case['id']}.json"
        output_file.write_text(
            json.dumps(test_case, ensure_ascii=False, indent=2),
            encoding="utf-8"
        )
        print(f"Generated: {output_file.name}")


def main():
    """Generate near-miss test cases from base test cases."""
    import argparse
    
    ap = argparse.ArgumentParser(description="Generate Track C near-miss test cases")
    ap.add_argument("--base-data", required=True, help="Directory with base test cases")
    ap.add_argument("--output", required=True, help="Output directory for near-miss test cases")
    ap.add_argument("--pattern", default="nt_*.json", help="Pattern to match base test files")
    args = ap.parse_args()
    
    base_dir = Path(args.base_data)
    output_dir = Path(args.output)
    
    # Find all base test cases
    base_files = sorted(base_dir.glob(args.pattern))
    
    if not base_files:
        print(f"No files found matching {args.pattern} in {base_dir}")
        return
    
    print(f"Generating near-miss variants from {len(base_files)} base test cases...")
    
    for base_file in base_files:
        print(f"\nProcessing {base_file.name}...")
        generate_nearmiss_from_file(base_file, output_dir)
    
    print(f"\nDone! Near-miss test cases written to {output_dir}")


if __name__ == "__main__":
    main()

