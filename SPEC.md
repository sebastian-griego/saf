# SPEC — What “same statement” means here

We evaluate **statement fidelity** (not truth). A candidate Lean proposition is accepted at **S0** iff:

1) It **parses and has type `Prop`** under the item’s listed `imports`, and
2) After S0 normalization, its string is **identical** to the canonical Lean string.

S0 normalization (applied to both sides):

- Collapse whitespace; trim ends.
- Canonicalize ASCII spellings → Unicode (`->`→`→`, `<->`→`↔`, `!=`→`≠`, `forall`→`∀`, `exists`→`∃`).
- Canonicalize binder style: `∀ a b : T, P` → `∀ (a b : T), P` (similarly for `∃`).
- Normalize spaces around punctuation/operators: `, : ( ) = ≤ ≥ ↔ → ≠`.

**Out of scope in S0:** α‑equivalence, definitional equality, and any deep semantic rewrites.
They belong in **S1** as a **tiny, versioned** list of safe equivalences applied to both sides *before* S0.

**S1 (later)** — candidate ideas (kept very small and audited):

- `x ≠ y` ↔ `¬ (x = y)`
- `a ≥ b` ↔ `b ≤ a` (canonicalize to `≤`)
- quantifier pushdown: `¬ ∃ x, P x` ↔ `∀ x, ¬ P x`

**Reporting:** For each item we save status (`accepted`/`rejected`), tier (`S0`), and on rejection a `reason` and a
**structured diff** (quantifiers, types, and operator skeleton). A summary includes counts and an error taxonomy.
