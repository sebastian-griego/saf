# Track C — Adversarial Near-Miss Testing

## Overview

Track C tests the **robustness** of statement auto-formalization systems by generating **adversarial near-miss** variants that are deliberately **non-equivalent** to the canonical statements. A reliable system should **reject** these variants.

## Goal

Measure **False Accept Rate on Near-Miss (FANM)** — the percentage of near-miss variants that are incorrectly accepted. For a reliable system, FANM should be ≈ 0.

## Near-Miss Variant Types

The generator creates variants by making minimal changes to canonical statements:

### 1. Operator Swaps
- `≤` ↔ `<` (less-than-or-equal to strict less-than)
- `≥` ↔ `>` (greater-than-or-equal to strict greater-than)
- `=` ↔ `≠` (equality to inequality)

### 2. Quantifier Swaps
- `∀` ↔ `∃` (universal to existential quantifier)

### 3. Type Swaps
- `ℕ` ↔ `ℤ` (natural numbers to integers)
- `ℕ` ↔ `ℝ` (natural numbers to real numbers)

### 4. Sign Flips
- `+` ↔ `-` (addition to subtraction)

### 5. Binder Swaps
- Swap variable order in binders: `∀ a b : T, P` → `∀ b a : T, P`

### 6. Condition Drops
- Remove conditions like `x ≠ 0`

## Test Case Format

Near-miss test cases have the same structure as regular test cases, with additional fields:

```json
{
  "id": "nt_0001_nearmiss_00_operator_swap_eq_to_neq",
  "domain": "nat",
  "nl": "For all natural numbers a and b, a + b ≠ b + a.",
  "lean": "∀ a b : ℕ, a + b = b + a",
  "candidate": "∀ a b : ℕ, a + b ≠ b + a",
  "imports": ["Mathlib/Data/Nat/Basic"],
  "should_reject": true,
  "nearmiss_type": "operator_swap_eq_to_neq",
  "base_id": "nt_0001"
}
```

### Fields

- `should_reject`: Always `true` for near-miss test cases
- `nearmiss_type`: Type of near-miss variant (e.g., `operator_swap_eq_to_neq`)
- `base_id`: ID of the original test case this variant was derived from
- `lean`: Canonical statement (ground truth)
- `candidate`: The near-miss variant (should be rejected)

## Generating Near-Miss Test Cases

Use the generator script to create near-miss variants from base test cases:

```bash
python harness/generate_nearmiss.py --base-data data --output data_nearmiss
```

This will:
1. Read all test cases from `data/`
2. Generate near-miss variants for each
3. Write them to `data_nearmiss/`

## Running Track C Evaluation

Run the harness on near-miss test cases:

```bash
python harness/check_s0.py --data data_nearmiss --project harness/lean_project --out reports/track_c.json
```

Or with S1 normalization:

```bash
python harness/check_s0.py --data data_nearmiss --project harness/lean_project --s1 --out reports/track_c_s1.json
```

## Metrics

The harness reports Track C metrics in the summary:

```json
{
  "summary": {
    "counts": {"accepted": 2, "rejected": 8},
    "total": 10,
    "track_c": {
      "total_nearmiss": 10,
      "false_accepts": 2,
      "correct_rejects": 8,
      "fanm": 0.2,
      "false_accept_details": [
        {
          "id": "nt_0001_nearmiss_04_operator_swap_eq_to_neq",
          "nearmiss_type": "operator_swap_eq_to_neq",
          "canonical": "∀ a b : ℕ, a + b = b + a",
          "candidate": "∀ a b : ℕ, a + b ≠ b + a",
          "canonical_norm": "...",
          "candidate_norm": "..."
        }
      ]
    }
  }
}
```

### Metrics Explained

- **total_nearmiss**: Total number of near-miss test cases
- **false_accepts**: Number of near-misses incorrectly accepted
- **correct_rejects**: Number of near-misses correctly rejected
- **fanm**: False Accept Rate on Near-Miss = `false_accepts / total_nearmiss`
- **false_accept_details**: Details of each false accept (for debugging)

## Interpreting Results

### Good System (FANM ≈ 0)
- Correctly rejects all near-miss variants
- High precision (doesn't accept wrong statements)

### Bad System (FANM > 0)
- Incorrectly accepts some near-miss variants
- Low precision (accepts statements that should be rejected)
- Check `false_accept_details` to see which variants were accepted

## Limitations

1. **Generator Coverage**: The generator may not cover all possible near-miss types
2. **Template Quality**: NL templates are basic; real-world NL may be more ambiguous
3. **Domain-Specific**: Some near-misses may be domain-specific (e.g., nat vs real)
4. **S1 Normalization**: S1 rules might normalize some near-misses incorrectly (this is a feature, not a bug — it tests S1's robustness)

## Future Work

1. **More Variant Types**: Add more sophisticated near-miss generators
2. **Domain-Specific**: Create domain-specific near-miss generators
3. **Human Evaluation**: Validate that near-misses are actually non-equivalent
4. **Adversarial Generation**: Use LLMs or other methods to generate more realistic near-misses

