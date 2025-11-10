# SAF V0 — Statement Auto‑Formalization Fidelity Harness (Windows + Python)

**What this is:** a tiny, transparent benchmark **and** harness to judge whether a candidate **Lean statement**
faithfully expresses the **same mathematical proposition** as a canonical one — **without proving it**.

- V0 implements **S0** (always on): type‑check + deterministic normalization + string equality.
- **S1** (optional): semantic rewrites enabled with `--s1` flag (e.g., `x ≠ y` → `¬ (x = y)`, `a ≥ b` → `b ≤ a`).

**Why this matters (short):** Formal proofs are easy to *verify* (they compile), but **statement auto‑formalization**
(the mapping NL → Lean *statement*) lacks a trusted benchmark. This harness fills that gap and produces clean
accept/reject decisions and error labels (syntax, unknown id, type mismatch, etc.).

> Truth requires a proof; **fidelity** is what we measure here.
> This is the missing evaluator that model builders and data pipelines can use before admitting NL↔Lean pairs.

---

## Quickstart (Windows + PowerShell)

1) **Install Lean 4 + elan** (toolchain manager). Ensure `lean` and `lake` are on PATH.
2) In *Developer PowerShell*, go to `harness/lean_project/`, then run:
   ```powershell
   lake update
   lake build
   lake env lean --version
   ```
   If you see version info, the Lean toolchain is working.

3) Back at repository root, run the harness:
   ```powershell
   python harness\check_s0.py --data .\data --project .\harness\lean_project
   python harness\check_s0.py --data .\data --project .\harness\lean_project --s1
   ```

4) Inspect `reports\demo_run.json` to see **accepted/rejected** items and an **error taxonomy** summary.

---

## Layout

```
saf_v0_new/
  README.md
  WHY.md                 # Why this is useful to the field
  SPEC.md                # What "same statement" means in S0/S1
  data/                  # Test items: canonical Lean + NL + imports
  data_challenge/        # Challenge test cases
  harness/
    check_s0.py          # Main harness: type-check → normalize → compare
    normalize.py         # S0/S1 normalization
    lean_project/        # Lean Lake project with mathlib
  scripts/
    run_demo.bat         # One-click run on Windows
    lean_env_check.ps1   # Quick Lean environment check
  reports/               # JSON reports written here
```

---

## How to read the decision

- **Type‑check pass**: candidate parses and has type `Prop` under the item’s imports.
- **S0 comparison**: after deterministic normalization, candidate string must match the canonical string exactly.
- **If mismatch**: normalized strings are included in the report for comparison.
- **If type‑check fails**: reason is `type_check_failed`.

> S0 is strict by design to be *obviously correct*. Use `--s1` to enable semantic rewrites for equivalent forms.

## Extending

- **Add items**: copy any file in `data/`, edit `nl`, `lean`, and `imports`. Keep NL unambiguous.
- **S1 rewrites**: add safe equivalence rules in `normalize.py`'s `_normalize_s1()` function.
