# SAF V0 — Statement Auto‑Formalization Fidelity Harness (Windows + Python)

**What this is:** a tiny, transparent benchmark **and** harness to judge whether a candidate **Lean statement**
faithfully expresses the **same mathematical proposition** as a canonical one — **without proving it**.

- V0 implements **S0** only: type‑check + deterministic normalization + string equality.
- You can later enable **S1**: a tiny, versioned bank of **safe equivalence rewrites** (e.g., `x ≠ y` ↔ `¬ (x = y)`).

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

3) Back at repository root, run the S0 harness:
   ```powershell
   python harness\check_s0.py --data .\data --project .\harness\lean_project
   ```

4) Inspect `reports\demo_run.json` to see **accepted/rejected** items and an **error taxonomy** summary.

---

## Layout

```
saf_v0_new/
  README.md
  WHY.md                 # Why this is useful to the field (and how teams use it)
  SPEC.md                # What “same statement” means in S0/S1
  data/                  # 15 seed items (ℕ/ℤ), canonical Lean + unambiguous NL + imports
  bank/
    s1_rewrites.txt      # placeholder; S1 is disabled by default
  harness/
    check_s0.py          # Annotated: type‑check → normalize → compare → error/diff report
    normalize.py         # Annotated: S0 normalization passes (ASCII→Unicode, binders, spacing)
    diff_explain.py      # Annotated: structured diffs when strings differ (types, quantifiers, ops)
    lean_project/
      lakefile.lean      # Minimal Lake project with mathlib dependency
      lean-toolchain     # Toolchain hint (adjust as needed)
      SAF/Prelude.lean   # Empty placeholder library
  prompts/
    ledger.jsonl         # (Optional) append prompt+output records if you use LLMs as *proposers*
  scripts/
    run_demo.bat         # One-click run on Windows
    lean_env_check.ps1   # Quick check that Lean resolves and runs
  reports/               # harness writes JSON reports here
```

---

## How to read the decision

- **Type‑check pass**: candidate parses and has type `Prop` under the item’s imports.
- **S0 comparison**: after deterministic normalization, candidate string must match the canonical string exactly.
- **If mismatch**: we attach a **structured diff** (quantifiers, variable types, and which logical operators appear).
- **If type‑check fails**: we classify into `syntax_error`, `unknown_identifier`, `type_mismatch`, etc.

> S0 is strict by design to be *obviously correct*. You can later enable S1 to iron out harmless surface differences.

---

## Using the harness with an LLM (optional, controlled)

- Keep a **prompt ledger** in `prompts/ledger.jsonl` (model name, prompt, output, timestamp).
- Treat the LLM as a **proposer**; **every** candidate must pass the deterministic S0/S1 gate.
- If you can’t read an output easily, don’t accept it. Ask the model to output a single `Prop` without tactics.

---

## Extending beyond V0

- **Add items**: copy any file in `data/`, edit `nl`, `lean`, and `imports`. Keep NL unambiguous.
- **Turn on S1**: implement a handful of safe rewrites in `normalize.py`, mirroring entries in `bank/s1_rewrites.txt`.
- **(Later) S2**: for decidable toy domains (e.g., bounded ℤ), add finite‑model sanity checks (separate metric).
