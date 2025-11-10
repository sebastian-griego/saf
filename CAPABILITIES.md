# Current Capabilities

## Overview

SAF V0 is a harness for testing **statement fidelity** (not truth) of Lean propositions. It type-checks candidate propositions and compares them to canonical forms after normalization.

## Current Status

**✅ Working**: The harness is fully functional with:
- Frozen toolchain (Lean 4.25.0-rc2, Mathlib commit `5d2ad00e3ff6eb9d93b3c52370a308ee24d5dbe8`)
- S0 normalization (always applied)
- S1 normalization (optional, conservative notation-level rewrites)
- Type-checking via Lean
- JSON report generation

## S0 Normalization (Always Applied)

S0 handles formatting and notation canonicalization:

1. **Whitespace collapse**: Multiple spaces → single space
2. **ASCII to Unicode**: 
   - `->` → `→`
   - `<->` → `↔`
   - `!=` → `≠`
   - `forall` → `∀`
   - `exists` → `∃`
3. **Binder canonicalization**: 
   - `∀ a b : T, P` → `∀ (a b : T), P`
   - `∀a : T, P` → `∀ (a : T), P` (handles no space after quantifier)
   - `∀ (a : T), P` → `∀ (a : T), P` (already canonical)
4. **Operator spacing**: Normalizes spaces around `,`, `:`, `=`, `≤`, `≥`, `↔`, `→`, `≠`, `∧`, `∨`

## S1 Normalization (Optional, `--s1` flag)

S1 applies **conservative, definitionally equivalent** notation rewrites:

1. **Not-Equals**: `x ≠ y` → `¬ (x = y)`
   - Definitional: `≠` is notation for `¬ (=)` in Lean
   
2. **Greater-Equal**: `a ≥ b` → `b ≤ a`
   - Definitional: `≥` is notation for flipped `≤` in Lean

**Not included** (by design):
- `¬ ∃ → ∀ ¬` (logical equivalence, not definitional)
- `a ≤ b ∧ b ≤ a ↔ a = b` (requires order structure)
- Binder variations (handled in S0)
- Comma/spacing (handled in S0)

See `bank/s1_rules.md` for detailed documentation.

## Test Results

### S0 Tests (`data/` directory)
- **20/20 accepted** (100%)
- All test cases pass with S0 normalization
- Includes tests for ASCII operators, whitespace, binder variations

### S1 Tests (`data_challenge/` directory)
- **2/8 accepted** with S1 (expected)
- Accepted:
  - `A_normalizer_accept_ascii`: ASCII operators (S0 handles this)
  - `H_neq_form_paraphrase`: `≠` normalization works correctly
- Rejected (correctly):
  - `B_binder_order_reject`: Variable order matters (`a b` vs `b a`)
  - `C_domain_drift_reject`: Type changes (`ℕ` vs `ℤ`)
  - `D_unknown_identifier_reject`: Type-check fails
  - `E_paren_noise_reject`: Extra parentheses (not normalized)
  - `F_quantifier_flip_reject`: Quantifier change (`∀` vs `∃`)
  - `G_ge_vs_le_paraphrase`: Sides flipped incorrectly (not equivalent)

## Known Limitations

1. **Parentheses**: Extra parentheses around expressions are not normalized (e.g., `(a + b) = (b + a)` vs `a + b = b + a`)
2. **Variable order**: Binder variable order matters (`∀ a b : T, P` vs `∀ b a : T, P`)
3. **Alpha-equivalence**: Not handled (variable renaming)
4. **Semantic equivalences**: Only definitional equivalences are handled in S1

## Usage

```powershell
# S0 only (default)
python harness/check_s0.py --data data --project harness/lean_project

# S1 enabled
python harness/check_s0.py --data data_challenge --project harness/lean_project --s1

# Custom output
python harness/check_s0.py --data data --project harness/lean_project --out reports/custom.json
```

## Files

- `harness/check_s0.py`: Main harness script
- `harness/normalize.py`: S0/S1 normalization implementation
- `bank/s1_rules.md`: S1 rule documentation
- `harness/lean_project/`: Lean project with frozen toolchain
- `data/`: Basic test cases (S0)
- `data_challenge/`: Challenge test cases (S1)

## Next Steps

Potential improvements:
1. Handle parentheses normalization in S0
2. Consider alpha-equivalence for variable renaming
3. Add more S1 rules (conservatively, with justification)
4. Improve error messages and diagnostics

