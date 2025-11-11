# WHY — What problem this solves (and for whom)

**Problem:** We can check whether a *proof* compiles in Lean, but we lack a trusted way to check whether an
*informal statement* was formalized into the **same mathematical proposition** in Lean. This “statement auto‑formalization”
evaluation gap makes it hard to measure progress, curate clean datasets, or debug systems that convert NL→Lean→proof.

**What SAF gives you:** a tiny, transparent harness to **accept** or **reject** a Lean statement *before proving*,
based on deterministic normalization (S0) and, later, a tiny bank of audited equivalences (S1). It’s **model‑agnostic**
and doubles as a **data gate** and **error analytics** tool.

- **Model builders** use it to track statement‑fidelity improvements separately from prover strength.
- **Data engineers** run it as an **admission gate** for NL↔Lean pairs (reject noisy pairs early).
- **Researchers** use the structured diffs to spot where formalizers go wrong (quantifiers/types/relations).

but **statement auto‑formalization lacks a good benchmark**. SAF fills that gap with something you can understand line‑by‑line
and grow safely. (See `SPEC.md` for precise acceptance rules.)
