# SAF V0 — Statement Auto‑Formalization Fidelity Harness (Windows + Python)

**What this is:** a tiny, transparent benchmark **and** harness to judge whether a candidate **Lean statement**
faithfully expresses the **same mathematical proposition** as a canonical one — **without proving it**.

- V0 implements **S0** (always on): type‑check + deterministic normalization + string equality.
- **S1** (optional): audited semantic rewrites enabled with `--s1` (alpha-renaming, definitional `≠`/`≥` rewrites, double-negation + De Morgan/quantifier pushdown, contrapositive, and deterministic `∧`/`∨`/binder flattening).
- **S3‑Lite** (optional): proof-based equivalence checking enabled with `--s3-lite` flag when S0/S1 normalization fails.
- **BEq+** (optional, "heavy" tier): statement-equivalence metric using deterministic tactics, enabled with `--beq-plus` flag.

**Why this matters (short):** Formal proofs are easy to *verify* (they compile), but **statement auto‑formalization**
(the mapping NL → Lean *statement*) lacks a trusted benchmark. This harness fills that gap and produces clean
accept/reject decisions based on type-checking and normalized string comparison.

> Truth requires a proof; **fidelity** is what we measure here.
> This is the missing evaluator that model builders and data pipelines can use before admitting NL↔Lean pairs.

---

## Quickstart (Windows + PowerShell)

**Frozen Toolchain**: This project uses **Lean 4.25.0-rc2** and **Mathlib4 commit `5d2ad00e3ff6eb9d93b3c52370a308ee24d5dbe8`** for reproducible results.

**Quick Reference**:
- Toolchain: `harness/lean_project/lean-toolchain` → `leanprover/lean4:v4.25.0-rc2`
- Mathlib: `harness/lean_project/lakefile.lean` → commit `5d2ad00e3ff6eb9d93b3c52370a308ee24d5dbe8`
- Dependencies: `harness/lean_project/lake-manifest.json` (committed to version control)

1) **Install elan** (Lean toolchain manager) and the exact toolchain:
   ```powershell
   # Install elan (if not already installed)
   Invoke-WebRequest https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 -OutFile elan-init.ps1
   .\elan-init.ps1
   
   # Install the exact Lean version
   elan toolchain install leanprover/lean4:v4.25.0-rc2
   elan default leanprover/lean4:v4.25.0-rc2
   ```

2) **Set up the Lean project** (dependencies are pinned in `lake-manifest.json`):
   ```powershell
   cd harness\lean_project
   lake update
   lake build
   lake env lean --version
   ```
   Should show: `Lean (version 4.25.0-rc2, ...)`

   **Note**: The toolchain is frozen in `lean-toolchain` and mathlib is pinned in `lakefile.lean` for reproducibility.
   
   **Performance Tip**: The harness automatically checks if the project is built before running tests to prevent slow automatic builds. You can also manually ensure it's built:
   ```powershell
   # From repository root
   .\scripts\ensure_built.ps1
   ```

   See [SETUP.md](SETUP.md) for detailed setup instructions and CI configuration.

3) **(Optional) Install Python dependencies** (for BEq+ support):
   ```powershell
   pip install lean-interact
   ```
   Note: BEq+ will work without this package (falls back to direct Lean implementation), but the lean-interact package provides the official BEq+ API.

4) Back at repository root, run the harness:
   ```powershell
   # S0 normalization (Python-based)
   python harness\check_s0.py --data .\data --project .\harness\lean_project
   
   # S1 normalization (semantic rewrites)
   python harness\check_s0.py --data .\data --project .\harness\lean_project --s1
   
   # Strict pretty-printing (Lean delaborator)
   python harness\check_s0.py --data .\data --project .\harness\lean_project --strict-pp
   
   # S3-Lite (proof-based equivalence)
   python harness\check_s0.py --data .\data --project .\harness\lean_project --s3-lite
   
   # Combined: S1 + S3-Lite
   python harness\check_s0.py --data .\data --project .\harness\lean_project --s1 --s3-lite --s3-classical --s3-timeout 10
   
   # BEq+ (heavy-tier equivalence)
   python harness\check_s0.py --data .\data --project .\harness\lean_project --beq-plus --beq-plus-timeout 30
   ```

5) Inspect `reports\demo_run.json` to see **accepted/rejected** items. Rejected items include a `reason` field
   (`type_check_failed` or `normalized_mismatch`) and normalized strings for comparison.

---

## Layout

```
saf_v0_new/
  README.md
  SPEC.md                # What "same statement" means in S0/S1
  WHY.md                 # Why this is useful to the field
  SETUP.md               # Detailed setup and toolchain documentation
  CAPABILITIES.md        # Detailed capabilities and limitations
  data/                  # Test items: canonical Lean + NL + imports
  data_challenge/        # Challenge test cases
  bank/
    s1_rules.md          # S1 normalization rules documentation
  harness/
    check_s0.py          # Main harness: type-check → normalize → compare
    normalize.py         # S0/S1 normalization
    lean_project/        # Lean Lake project with mathlib
  scripts/
    run_demo.bat         # One-click run on Windows
    lean_env_check.ps1   # Quick Lean environment check
    verify_toolchain.ps1 # Verify frozen toolchain setup
  .github/workflows/     # CI workflow for automated testing
  reports/               # JSON reports written here
```

---

## How to read the decision

The harness returns `accepted` or `rejected` for each test case:

- **Type‑check pass**: candidate must parse and have type `Prop` under the item's imports.
- **Normalization comparison**: after deterministic normalization (S0 or S1), candidate string must match the canonical string exactly.
- **Rejection reasons**:
  - `type_check_failed`: candidate failed to type-check (syntax error, unknown identifier, type mismatch, etc.)
  - `normalized_mismatch`: type-check passed but normalized strings don't match (includes both normalized strings in the report)

> S0 is strict by design to be *obviously correct*. Use `--s1` to enable definitionally equivalent notation rewrites.

## Toolchain & Reproducibility

**Frozen Configuration** (for deterministic S0 normalization and strict PP):
- **Lean**: `v4.25.0-rc2` (specified in `harness/lean_project/lean-toolchain`)
- **Mathlib4**: Commit `5d2ad00e3ff6eb9d93b3c52370a308ee24d5dbe8` (pinned in `lakefile.lean`)
- **All dependencies**: Locked in `lake-manifest.json` (**must be committed to version control**)

The toolchain is frozen to ensure reproducible results across different machines and CI environments. See [SETUP.md](SETUP.md) for detailed setup instructions and verification steps.

**Strict Pretty-Printing** (optional, `--strict-pp` flag):
- Uses Lean's delaborator system with pinned PP options for deterministic output
- PP options: `pp.notation=true`, `pp.foralls=true`, `pp.parens=true`, `pp.unicode=true`, `pp.implicit=false`, `pp.explicit=false`
- Ensures stable equality across machines by using Lean's native pretty-printing
- PP options are logged in the run manifest for reproducibility
- See [PP_PROFILE.md](PP_PROFILE.md) for detailed documentation

## Current Capabilities

**S0 Normalization** (default, Python-based):
- Whitespace collapse, ASCII→Unicode conversion
- Binder canonicalization (`∀ a : T, P` → `∀ (a : T), P`)
- Operator spacing normalization
- **Test results**: 20/20 accepted in `data/` directory

**Strict Pretty-Printing** (optional, `--strict-pp` flag):
- Uses Lean's delaborator with pinned PP options for deterministic output
- Replaces Python normalization with Lean's native pretty-printing
- Ensures stable equality across machines by using Lean's internal representation
- PP options are documented in [PP_PROFILE.md](PP_PROFILE.md) and logged in reports

**S1 Normalization** (optional, `--s1` flag):
- α-renames binders before/after rewrites for deterministic scopes.
- Definitional notation rewrites: `x ≠ y` → `¬ (x = y)` and `a ≥ b` → `b ≤ a`.
- Classical logic rewrites applied recursively: double negation, De Morgan, quantifier negation, and contrapositive.
- Structural canonization: flatten and sort `∧`/`∨` trees and combine like quantifiers (binder normalization).
- **Test results**: 2/8 accepted in `data_challenge/` (correctly rejects non-equivalent forms)
- See [bank/s1_rules.md](bank/s1_rules.md) for the full audited rule bank and proofs
- See [CAPABILITIES.md](CAPABILITIES.md) for detailed capabilities and limitations

**S3‑Lite** (optional, `--s3-lite` flag):
- Proof-based equivalence checking when S0/S1 normalization fails
- Attempts to prove `canonical ↔ candidate` using Lean tactics
- **Permitted tactics**: `rfl` (definitional equality), `simp_all` with logic-only lemmas (`iff_true`, `iff_false`, `not_forall`, `not_exists`, `and_assoc`, `and_comm`, `or_comm`, `not_and`, `not_or`, `imp_true`, `true_imp`), `constructor`-based proofs, and classical reasoning with `contrapose!` (attempted by default as fallback)
- **Classical reasoning**: Attempted by default as a fallback tactic; `--s3-classical` flag records preference in reports
- **CLI flags**: `--s3-lite` (enable S3-Lite), `--s3-classical` (record classical preference), `--s3-timeout N` (timeout in seconds, default: 5)
- **Important**: S3-Lite never changes S0/S1 accept/reject decisions; it only adds `s3_lite_attempted: true` and `s3_lite_succeeded: true` fields to the report when enabled

**BEq+** (optional, `--beq-plus` flag, "heavy" tier):
- Statement-equivalence metric that proves each direction (P → Q and Q → P) with a deterministic bundle of tactics
- Based on the BEq+ metric from "Reliable Evaluation and Benchmarks for Statement Autoformalization" (EMNLP 2025)
  - Paper: https://aclanthology.org/2025.emnlp-main.907.pdf
  - Code: https://github.com/augustepoiroux/LeanInteract
- **Implementation Status**: ⚠️ **PLACEHOLDER** - Currently uses a simplified fallback implementation
  - Attempts to use lean-interact package if available, but the API may not match the actual implementation
  - Falls back to a simplified direct Lean implementation (rfl, assumption, simp_all)
  - **TODO**: Align with the official BEq+ implementation from LeanInteract repository
- **CLI flags**: `--beq-plus` (enable BEq+), `--beq-plus-timeout N` (timeout in seconds, default: 30)
- **Dependencies**: Optional `lean-interact` package (install with `pip install lean-interact`)
- **Use case**: Catches equivalences missed by normalization and S3-Lite; suitable for research-level math evaluation
- **Note**: BEq+ is distinct from Lean's `BEq` typeclass (boolean equality `==`); BEq+ is for mathematical equivalence

## Extending

- **Add items**: copy any file in `data/`, edit `nl`, `lean`, and `imports`. Keep NL unambiguous.
- **S1 rewrites**: add safe equivalence rules in `normalize.py`'s `_normalize_s1()` function.
