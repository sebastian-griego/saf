# Current Capabilities

## Overview

SAF V0 is a harness for testing **statement fidelity** (not truth) of Lean propositions. It type-checks candidate propositions and compares them to canonical forms after normalization.

## Current Status

**✅ Working**: The harness is fully functional with:
- Frozen toolchain (Lean 4.25.0-rc2, Mathlib commit `5d2ad00e3ff6eb9d93b3c52370a308ee24d5dbe8`)
- S0 normalization (always applied)
- S1 normalization (optional, conservative notation-level rewrites)
- S3-Lite proof-based equivalence checking (optional)
- BEq+ statement-equivalence metric (optional, "heavy" tier)
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

S1 applies **audited, deterministic** rewrites to both canonical and candidate propositions:

1. **α-renaming**: Canonicalizes bound variable names before and after rewrites so scopes are deterministic.
2. **Definitional notation rewrites**: `x ≠ y` → `¬ (x = y)` and `a ≥ b` → `b ≤ a`.
3. **Classical logic rewrites (recursive)**: double negation elimination, De Morgan, quantifier negation (`¬∃`/`¬∀` pushdowns), and contrapositive (`P → Q` ↦ `¬Q → ¬P`).
4. **Structural canonization**: Flatten and lexicographically sort `∧`/`∨` trees and merge like quantifiers (binder normalization), then re-run α-renaming.

**Not included** (by design):
- Rewrites that require extra structure (e.g., `a ≤ b ∧ b ≤ a ↔ a = b` depends on antisymmetry)
- Domain-specific or arithmetic facts beyond pure logic/notation
- Binder/spacing tweaks already handled in S0

See `bank/s1_rules.md` for the full rule bank, justification, and tests.

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
3. **Alpha-equivalence**: Handled in S1 (bound variables are renamed to canonical form)
4. **Semantic equivalences**: S1 only covers definitional + classical logic tautologies; structure-dependent rewrites remain out of scope

## S3-Lite (Optional, `--s3-lite` flag)

S3-Lite provides proof-based equivalence checking when S0/S1 normalization fails:

- **Approach**: Attempts to prove `canonical ↔ candidate` using Lean tactics
- **Permitted tactics**: `rfl` (definitional equality), `simp_all` with logic-only lemmas, `constructor`-based proofs, classical reasoning
- **Timeout**: Default 5 seconds (configurable with `--s3-timeout`)
- **Classical reasoning**: Optional with `--s3-classical` flag

## BEq+ (Optional, `--beq-plus` flag, "heavy" tier)

BEq+ is a statement-equivalence metric that proves each direction (P → Q and Q → P) with a deterministic bundle of tactics:

- **Reference**: "Reliable Evaluation and Benchmarks for Statement Autoformalization" (EMNLP 2025)
  - Paper: https://aclanthology.org/2025.emnlp-main.907.pdf
  - Code: https://github.com/augustepoiroux/LeanInteract
- **Implementation Status**: ⚠️ **PLACEHOLDER** - Currently uses a simplified fallback implementation
  - Attempts to use lean-interact package if available, but the API may not match
  - Falls back to a simplified direct Lean implementation
  - **TODO**: Align with the official BEq+ implementation from LeanInteract repository
- **Current Fallback Tactics**: Deterministic bundle (rfl, assumption, simp_all) applied to both directions separately
- **Timeout**: Default 30 seconds (configurable with `--beq-plus-timeout`)
- **Dependencies**: Optional `lean-interact` package (install with `pip install lean-interact`)
- **Use case**: Catches equivalences missed by normalization and S3-Lite; suitable for research-level math evaluation
- **Note**: BEq+ is distinct from Lean's `BEq` typeclass (boolean equality `==`); BEq+ is for mathematical equivalence

### BEq+ Implementation Details

**Current Implementation (Placeholder)**:
BEq+ works by:
1. Proving the forward direction: `canonical → candidate`
2. Proving the backward direction: `candidate → canonical`
3. Combining both directions to show equivalence: `canonical ↔ candidate`

The current fallback tactic bundle tries:
- `rfl` (definitional equality)
- `assumption` (use hypothesis)
- `simp_all` (simplification - may be too permissive)

**Official BEq+ (from paper)**:
According to the paper, BEq+ is:
- Deterministic
- Runs efficiently on CPU (no 20B LLM prover required)
- Proves both directions separately
- Correlates strongly with human judgment
- More sophisticated than the current fallback implementation

**Next Steps**:
1. Check the actual BEq+ implementation in https://github.com/augustepoiroux/LeanInteract
2. Verify the correct API for calling BEq+ from Python
3. Update the implementation to use the official BEq+ tactic bundle
4. Ensure the implementation matches the paper's specifications

## Usage

```powershell
# S0 only (default)
python harness/check_s0.py --data data --project harness/lean_project

# S1 enabled
python harness/check_s0.py --data data_challenge --project harness/lean_project --s1

# S3-Lite enabled
python harness/check_s0.py --data data --project harness/lean_project --s3-lite

# BEq+ enabled (heavy tier)
python harness/check_s0.py --data data --project harness/lean_project --beq-plus

# Combined: S1 + S3-Lite + BEq+
python harness/check_s0.py --data data --project harness/lean_project --s1 --s3-lite --beq-plus

# Custom output and timeouts
python harness/check_s0.py --data data --project harness/lean_project --out reports/custom.json --beq-plus-timeout 60
```

## Files

- `harness/check_s0.py`: Main harness script
- `harness/normalize.py`: S0/S1 normalization implementation
- `bank/s1_rules.md`: S1 rule documentation
- `harness/lean_project/`: Lean project with frozen toolchain
- `data/`: Basic test cases (S0)
- `data_challenge/`: Challenge test cases (S1)

## Evaluation Tiers

The harness supports multiple evaluation tiers, applied in order:

1. **S0** (always applied): Type-check + normalization + string equality
2. **S1** (optional): Semantic rewrites (definitional equivalences)
3. **S3-Lite** (optional): Proof-based equivalence with logic-only tactics
4. **BEq+** (optional, "heavy" tier): Deterministic tactic bundle for both directions

Each tier is more powerful but also more computationally expensive. BEq+ is the "heavy" tier suitable for research-level math evaluation.

## Next Steps

Potential improvements:
1. Handle parentheses normalization in S0
2. Add more S1 rules (conservatively, with justification)
3. Improve error messages and diagnostics
4. Consider handling variable order normalization (if semantically safe)
5. Integrate official BEq+ implementation from lean-interact (when API is finalized)

