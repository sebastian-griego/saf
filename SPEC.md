# SPEC — What "same statement" means here

We evaluate **statement fidelity** (not truth). A candidate Lean proposition is accepted at **S0** iff:

1) It **parses and has type `Prop`** under the item's listed `imports`, and
2) After S0 normalization, its string is **identical** to the canonical Lean string.

## S0 Normalization (Python-based, default)

S0 normalization (applied to both sides):

- Collapse whitespace; trim ends.
- Canonicalize ASCII spellings → Unicode (`->`→`→`, `<->`→`↔`, `!=`→`≠`, `forall`→`∀`, `exists`→`∃`).
- Canonicalize binder style: `∀ a b : T, P` → `∀ (a b : T), P` (similarly for `∃`).
- Normalize spaces around punctuation/operators: `, : ( ) = ≤ ≥ ↔ → ≠`.

**Out of scope in S0:** α‑equivalence, definitional equality, and any deep semantic rewrites.
They belong in **S1** as a **tiny, versioned** list of safe equivalences applied to both sides.

## Strict Pretty-Printing (Lean delaborator, `--strict-pp` flag)

When using the `--strict-pp` flag, S0 uses Lean's delaborator system with pinned PP options instead of Python-based normalization:

- **Method**: Lean's native pretty-printer (delaborator) with pinned PP options
- **PP Options**: `pp.notation=true`, `pp.foralls=true`, `pp.parens=true`, `pp.unicode=true`, `pp.implicit=false`, `pp.explicit=false`
- **Determinism**: Ensures stable output across machines by using Lean's internal representation
- **Advantages**: Respects Lean's notation system, guaranteed consistency with type-checker
- **Documentation**: See [PP_PROFILE.md](PP_PROFILE.md) for detailed PP options profile

The strict PP mode replaces Python string normalization with Lean's native pretty-printing, ensuring that expressions are displayed using Lean's internal representation and notation system. PP options are logged in the run manifest for reproducibility.

**S1 (implemented)** — current rules (kept very small and audited):

- **α-renaming**: Canonicalizes bound variable names before and after rewrites.
- **Definitional notation rewrites**: `x ≠ y` ↔ `¬ (x = y)` and `a ≥ b` ↔ `b ≤ a`.
- **Classical logic rewrites**: double negation, De Morgan, quantifier negation (`¬∃`/`¬∀` pushdowns), and contrapositive (`P → Q` ↔ `¬Q → ¬P`), applied recursively.
- **Structural canonization**: Flatten + sort `∧`/`∨` trees and merge same-type quantifiers, then re-run α-renaming.

**S1 (future candidates)** — additions require kernel-level justification and new tests; currently no pending rules.

**Reporting:** For each item we save status (`accepted`/`rejected`), tier (`S0`), and on rejection a `reason` and a
**structured diff** (quantifiers, types, and operator skeleton). A summary includes counts and an error taxonomy.
