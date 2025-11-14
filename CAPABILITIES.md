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
- **Implementation Status**: ✅ Uses the official LeanInteract BEq+ algorithm when the `lean-interact` package is installed (AutoLeanServer, Algorithm 1 from the paper). Falls back to a conservative Lean snippet otherwise.
- **Fallback tactic bundle** (deterministic, immediate-fail):
  - `exact h` (definitional equality), `assumption`
  - `simp only [and_comm, or_comm, add_comm, mul_comm]` for light commutativity rewrites
- **Timeout**: Default 30 seconds per BEq+ attempt (configurable with `--beq-plus-timeout`)
- **Global budget**: `--max-beq-plus-calls` caps how many BEq+ invocations run in a harness pass (skip+log once exhausted)
- **Dependencies**: `pip install lean-interact` to enable the official algorithm; fallback path requires only Lean/Lake
- **Use case**: Catches equivalences missed by normalization and S3-Lite; suitable for research-level math evaluation
- **Classical reasoning**: Shares the `--s3-classical` flag—when set, BEq+ opens `Classical` in both official and fallback modes
- **Note**: BEq+ is distinct from Lean's `BEq` typeclass (boolean equality `==`); BEq+ is for mathematical equivalence

### BEq+ Implementation Details

**Current Implementation**:
1. Prefer the LeanInteract BEq+ helper (Algorithm 1) via `lean_interact.AutoLeanServer`, mirroring the paper exactly.
2. If LeanInteract is unavailable or fails, fall back to the local deterministic snippet that attempts each direction separately using the conservative bundle above.
3. Each invocation records success/failure, direction info, strategy, timing, and logs for auditability.

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

# Combined: S1 + S3-Lite + BEq+ (with 60s BEq+ timeout, cap at 200 calls)
python harness/check_s0.py --data data --project harness/lean_project \
  --s1 --s3-lite --beq-plus \
  --beq-plus-timeout 60 \
  --max-beq-plus-calls 200

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

