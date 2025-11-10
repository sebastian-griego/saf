# S1 Normalization Rules

**Version**: 1.1  
**Last Updated**: 2025-01-10

## Philosophy

S1 rules are **notation-level equalities** that are:
1. **Definitionally equivalent** in Lean (same meaning at the kernel level), OR
2. **Universally valid** without extra hypotheses (always true, no structure needed), OR
3. **Syntactic equivalences** that don't change meaning (like α-renaming of bound variables)

S1 rules are applied to **both** canonical and candidate propositions before comparison, ensuring we accept equivalent notation variants while remaining conservative.

## Rules

### Rule 0: Alpha-Renaming of Bound Variables
**Transformation**: Rename bound variables in quantifiers to canonical names (x₁, x₂, x₃, ...)

**Source**: Standard α-equivalence in lambda calculus and dependent type theory.

**Justification**: Bound variable names are irrelevant to meaning. Renaming `∀ (a : ℕ), P a` to `∀ (x₁ : ℕ), P x₁` preserves semantics. Each quantifier scope gets fresh canonical names starting from x₁, ensuring α-equivalent propositions are recognized as equivalent.

**Example**:
- Input: `∀ (a : ℕ), ∃ (b : ℕ), a = b`
- Output: `∀ (x₁ : ℕ), ∃ (x₁ : ℕ), x₁ = x₁`

**Note**: This rule is applied first in S1 normalization, before other rules. It handles nested quantifiers correctly, with each scope getting its own fresh canonical variable names.

### Rule 1: Not-Equals to Negated Equality
**Transformation**: `x ≠ y` → `¬ (x = y)`

**Source**: Lean core definition. The `≠` operator is defined as notation for `fun x y => ¬ (x = y)`.

**Justification**: Definitionally equivalent in Lean. `x ≠ y` is literally `¬ (x = y)` at the kernel level.

**Example**:
- Input: `∀ (x₁ x₂ : ℕ), x₁ ≠ x₂`
- Output: `∀ (x₁ x₂ : ℕ), ¬ (x₁ = x₂)`

### Rule 2: Greater-Equal to Flipped Less-Equal
**Transformation**: `a ≥ b` → `b ≤ a`

**Source**: Lean core definition. The `≥` operator is defined as notation for `fun a b => b ≤ a` (via `GE.ge`).

**Justification**: Definitionally equivalent in Lean. `a ≥ b` is literally `b ≤ a` at the kernel level.

**Example**:
- Input: `∀ (x₁ x₂ : ℕ), x₁ ≥ x₂`
- Output: `∀ (x₁ x₂ : ℕ), x₂ ≤ x₁`

## Out of Scope

The following are **NOT** included in S1, as they require additional structure or are logical equivalences rather than definitional:

- `a ≤ b ∧ b ≤ a ↔ a = b` — requires an order structure (antisymmetry)
- `¬ ∃ (x : T), P x ↔ ∀ (x : T), ¬ P x` — logical equivalence (De Morgan's law), not definitional
- Binder sugar variations — already handled in S0 (`∀ x, P` vs `∀ (x : T), P`)
- Comma/spacing differences — already handled in S0
- ASCII to Unicode — already handled in S0
- Variable order in binders — `∀ a b : T, P` vs `∀ b a : T, P` are different (order matters in dependent types)

## Implementation

Rules are applied in order:
1. Rule 0 (Alpha-renaming) is applied first to normalize bound variable names
2. Rule 2 (Greater-Equal) is applied before Rule 1 to avoid conflicts
3. Rule 1 (Not-Equals) is applied last
4. Spacing is re-normalized after all rules

Both canonical and candidate propositions undergo the same transformations, ensuring equivalent notation is accepted.

## Testing

See `data_challenge/H_neq_form_paraphrase.json` and `data_challenge/G_ge_vs_le_paraphrase.json` for test cases.

## Versioning

When adding new rules:
1. Document the rule with source and justification
2. Add test cases
3. Update version number
4. Ensure rule is definitionally equivalent or universally valid

