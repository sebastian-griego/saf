# S1 Normalization Rules

**Version**: 3.0  
**Last Updated**: 2025-01-11

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

### Rule 3: Double Negation Elimination
**Transformation**: `¬¬P` → `P`

**Source**: Classical logic. Double negation elimination is valid in classical logic (which Lean uses by default).

**Justification**: Universally valid logical equivalence. `¬¬P` is logically equivalent to `P` in classical logic.

**Example**:
- Input: `¬¬ (x = y)`
- Output: `x = y`

### Rule 4: De Morgan's Laws
**Transformation**: 
- `¬(P ∧ Q)` → `(¬P ∨ ¬Q)`
- `¬(P ∨ Q)` → `(¬P ∧ ¬Q)`

**Source**: Classical logic (De Morgan's laws).

**Justification**: Universally valid logical equivalences. These are fundamental laws of classical logic that hold without any domain assumptions.

**Example**:
- Input: `¬(P ∧ Q)`
- Output: `(¬P ∨ ¬Q)`
- Input: `¬(P ∨ Q)`
- Output: `(¬P ∧ ¬Q)`

**Note**: Operands are sorted lexicographically for deterministic normalization.

### Rule 5: Quantifier Negation
**Transformation**:
- `¬∃ (x : T), P x` → `∀ (x : T), ¬P x`
- `¬∀ (x : T), P x` → `∃ (x : T), ¬P x`

**Source**: Classical logic (quantifier negation laws).

**Justification**: Universally valid logical equivalences. These are standard quantifier negation laws that hold in classical logic.

**Example**:
- Input: `¬∃ (x : ℕ), x > 0`
- Output: `∀ (x : ℕ), ¬(x > 0)`
- Input: `¬∀ (x : ℕ), x = 0`
- Output: `∃ (x : ℕ), ¬(x = 0)`

### Rule 6: Contrapositive Normalization
**Transformation**: `P → Q` → `¬Q → ¬P`

**Source**: Classical logic (contrapositive law).

**Justification**: Universally valid logical equivalence. The contrapositive of an implication is logically equivalent to the original.

**Example**:
- Input: `P → Q`
- Output: `¬Q → ¬P`

**Note**: All implications are normalized to contrapositive form for deterministic canonical representation.

### Rule 7: Commutativity Normalization
**Transformation**: 
- `P ∧ Q` → `Q ∧ P` (normalized to lexicographic order)
- `P ∨ Q` → `Q ∨ P` (normalized to lexicographic order)

**Source**: Classical logic (commutativity of conjunction and disjunction).

**Justification**: Universally valid logical equivalences. Conjunction and disjunction are commutative operations.

**Example**:
- Input: `Q ∧ P`
- Output: `P ∧ Q` (if `P < Q` lexicographically)
- Input: `B ∨ A`
- Output: `A ∨ B` (if `A < B` lexicographically)

**Note**: Operands are sorted lexicographically by their string representation for deterministic normalization. This ensures that `P ∧ Q` and `Q ∧ P` normalize to the same canonical form.

### Rule 8: Associativity Normalization
**Transformation**: 
- `(P ∧ Q) ∧ R` → `P ∧ Q ∧ R` (flatten nested conjunctions)
- `(P ∨ Q) ∨ R` → `P ∨ Q ∨ R` (flatten nested disjunctions)

**Source**: Classical logic (associativity of conjunction and disjunction).

**Justification**: Universally valid logical equivalences. Conjunction and disjunction are associative operations, so nested structures can be flattened without changing meaning.

**Example**:
- Input: `(P ∧ Q) ∧ R`
- Output: `P ∧ Q ∧ R` (after flattening, then sorted lexicographically by Rule 7)
- Input: `A ∨ (B ∨ C)`
- Output: `A ∨ B ∨ C` (after flattening, then sorted lexicographically by Rule 7)

**Note**: Associativity normalization (Rule 8) is applied before commutativity normalization (Rule 7), so nested structures are first flattened, then operands are sorted lexicographically for deterministic canonical form.

### Rule 9: Binder Normalization
**Transformation**: 
- `∀ (x : T), ∀ (y : U), P` → `∀ (x : T) (y : U), P` (flatten nested universal quantifiers)
- `∃ (x : T), ∃ (y : U), P` → `∃ (x : T) (y : U), P` (flatten nested existential quantifiers)

**Source**: Lean syntax equivalence. In Lean, `∀ (x : T) (y : U), P` is definitionally equivalent to `∀ (x : T), ∀ (y : U), P` when the types are independent.

**Justification**: Definitionally equivalent in Lean. When quantifiers of the same type are nested and the inner quantifier's type doesn't depend on the outer variable, the flattened form is equivalent. This normalization moves binders into a canonical shape.

**Example**:
- Input: `∀ (x : ℕ), ∀ (y : ℕ), x = y`
- Output: `∀ (x₁ : ℕ) (x₂ : ℕ), x₁ = x₂` (after alpha-renaming and binder normalization)
- Input: `∃ (a : ℕ), ∃ (b : ℕ), a + b = 0`
- Output: `∃ (x₁ : ℕ) (x₂ : ℕ), x₁ + x₂ = 0` (after alpha-renaming and binder normalization)

**Note**: This rule only applies when the nested quantifiers are of the same type (both `∀` or both `∃`). Mixed quantifiers like `∀ (x : T), ∃ (y : U), P` are not normalized, as the order matters. The rule is applied recursively, so deeply nested quantifiers are flattened step by step.

## Out of Scope

The following are **NOT** included in S1, as they require additional structure or are not universally valid:

- `a ≤ b ∧ b ≤ a ↔ a = b` — requires an order structure (antisymmetry)
- Binder sugar variations — already handled in S0 (`∀ x, P` vs `∀ (x : T), P`)
- Comma/spacing differences — already handled in S0
- ASCII to Unicode — already handled in S0
- Variable order in binders — `∀ a b : T, P` vs `∀ b a : T, P` are different (order matters in dependent types)

## Implementation

Rules are applied in order:
1. **Rule 0** (Alpha-renaming) is applied first to normalize bound variable names
2. **Rule 2** (Greater-Equal) is applied before Rule 1 to avoid conflicts
3. **Rule 1** (Not-Equals) converts `≠` to negated equality
4. **Rule 3** (Logical Structure Normalization) applies Rules 3-9 recursively:
   - **Rule 3**: Double negation elimination (`¬¬P → P`)
   - **Rule 4**: De Morgan's laws (push negations inward)
   - **Rule 5**: Quantifier negation (push negations through quantifiers)
   - **Rule 6**: Contrapositive normalization (convert implications to contrapositive form)
   - **Rule 8**: Associativity normalization (flatten nested `∧` and `∨` structures)
   - **Rule 7**: Commutativity normalization (sort `∧` and `∨` operands lexicographically)
   - **Rule 9**: Binder normalization (flatten nested quantifiers of same type)
5. Spacing is re-normalized after all rules

The logical structure normalization (Rules 3-9) is applied recursively to handle nested structures. Associativity (Rule 8) is applied before commutativity (Rule 7) to ensure nested structures are flattened before sorting. All rules are deterministic, ensuring that equivalent propositions normalize to the same canonical form.

Both canonical and candidate propositions undergo the same transformations, ensuring equivalent notation is accepted.

## Testing

See `data_challenge/H_neq_form_paraphrase.json` and `data_challenge/G_ge_vs_le_paraphrase.json` for test cases.

## Versioning

When adding new rules:
1. Document the rule with source and justification
2. Add test cases
3. Update version number
4. Ensure rule is definitionally equivalent or universally valid

