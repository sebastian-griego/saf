# S1 Normalization Rules

**Version**: 1.0  
**Last Updated**: 2025-01-10

## Philosophy

S1 rules are **notation-level equalities** that are:
1. **Definitionally equivalent** in Lean (same meaning at the kernel level), OR
2. **Universally valid** without extra hypotheses (always true, no structure needed)

S1 rules are applied to **both** canonical and candidate propositions before comparison, ensuring we accept equivalent notation variants while remaining conservative.

## Rules

### Rule 1: Not-Equals to Negated Equality
**Transformation**: `x ≠ y` → `¬ (x = y)`

**Source**: Lean core definition. The `≠` operator is defined as notation for `fun x y => ¬ (x = y)`.

**Justification**: Definitionally equivalent in Lean. `x ≠ y` is literally `¬ (x = y)` at the kernel level.

**Example**:
- Input: `∀ a b : ℕ, a ≠ b`
- Output: `∀ (a b : ℕ), ¬ (a = b)`

### Rule 2: Greater-Equal to Flipped Less-Equal
**Transformation**: `a ≥ b` → `b ≤ a`

**Source**: Lean core definition. The `≥` operator is defined as notation for `fun a b => b ≤ a` (via `GE.ge`).

**Justification**: Definitionally equivalent in Lean. `a ≥ b` is literally `b ≤ a` at the kernel level.

**Example**:
- Input: `∀ a b : ℕ, a ≥ b`
- Output: `∀ (a b : ℕ), b ≤ a`

## Out of Scope

The following are **NOT** included in S1, as they require additional structure or are logical equivalences rather than definitional:

- `a ≤ b ∧ b ≤ a ↔ a = b` — requires an order structure (antisymmetry)
- `¬ ∃ (x : T), P x ↔ ∀ (x : T), ¬ P x` — logical equivalence (De Morgan's law), not definitional
- Binder sugar variations — already handled in S0 (`∀ x, P` vs `∀ (x : T), P`)
- Comma/spacing differences — already handled in S0
- ASCII to Unicode — already handled in S0

## Implementation

Rules are applied in order, then spacing is re-normalized. Both canonical and candidate propositions undergo the same transformations, ensuring equivalent notation is accepted.

## Testing

See `data_challenge/H_neq_form_paraphrase.json` and `data_challenge/G_ge_vs_le_paraphrase.json` for test cases.

## Versioning

When adding new rules:
1. Document the rule with source and justification
2. Add test cases
3. Update version number
4. Ensure rule is definitionally equivalent or universally valid

