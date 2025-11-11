# Pretty-Printing Profile for Strict Tier

This document specifies the exact pretty-printing (PP) options used for deterministic output in the strict tier of the SAF V0 harness.

## Overview

The strict tier uses Lean's built-in delaborator system with pinned PP options to ensure that expressions are pretty-printed deterministically across different machines and environments. This replaces Python-based string normalization with Lean's native pretty-printing, which respects Lean's internal representation and notation system.

## PP Options Profile

The following PP options are set when using `--strict-pp`:

| Option | Value | Description |
|--------|-------|-------------|
| `pp.notation` | `true` | Use defined notations (→, ↔, ∀, ∃, etc.) |
| `pp.foralls` | `true` | Show forall quantifiers explicitly |
| `pp.parens` | `true` | Add parentheses where needed for clarity |
| `pp.unicode` | `true` | Use Unicode characters (→, ↔, ∀, ∃, etc.) |
| `pp.implicit` | `false` | Hide implicit arguments |
| `pp.explicit` | `false` | Hide explicit type annotations |

## Implementation

The PP options are set in the generated Lean scripts before defining propositions. The script structure is:

```lean
import <required_imports>

set_option pp.notation true
set_option pp.foralls true
set_option pp.parens true
set_option pp.unicode true
set_option pp.implicit false
set_option pp.explicit false

def _prop : Prop :=
  <proposition>

#print _prop
```

The `#print` command outputs the definition with the specified PP options applied, and the harness extracts the pretty-printed expression from the output.

## Rationale

### Why Use Lean's Pretty-Printer?

1. **Deterministic Output**: Lean's delaborator system ensures consistent output across machines when the same PP options are used.
2. **Notation Respect**: Lean's pretty-printer respects the notation system, ensuring that expressions are displayed using the intended notations.
3. **Version Consistency**: By pinning both Lean version and PP options, we ensure reproducible results across different environments.

### Why These Specific Options?

- **`pp.notation = true`**: We want to use Lean's notation system (→, ↔, ∀, ∃) for readability and consistency.
- **`pp.foralls = true`**: Explicit forall quantifiers ensure clarity and deterministic output.
- **`pp.parens = true`**: Parentheses help disambiguate expressions and ensure consistent parsing.
- **`pp.unicode = true`**: Unicode symbols (→, ↔, ∀, ∃) are more readable and are the standard in Lean.
- **`pp.implicit = false`**: Implicit arguments are hidden for cleaner output, focusing on the proposition structure.
- **`pp.explicit = false`**: Type annotations are hidden for cleaner output, as types are already known from context.

## Toolchain Requirements

The strict PP mode requires:

- **Lean Version**: `leanprover/lean4:v4.25.0-rc2` (pinned in `harness/lean_project/lean-toolchain`)
- **Mathlib Version**: Commit `5d2ad00e3ff6eb9d93b3c52370a308ee24d5dbe8` (pinned in `harness/lean_project/lakefile.lean`)

These versions are pinned to ensure that PP behavior is consistent across different machines. Lean releases may change default PP behaviors, so pinning the version is critical for reproducibility.

## Usage

To use the strict PP mode, add the `--strict-pp` flag when running the harness:

```powershell
python harness\check_s0.py --data .\data --project .\harness\lean_project --strict-pp
```

The harness will:
1. Type-check the candidate proposition
2. Pretty-print both canonical and candidate propositions using Lean's delaborator with the specified PP options
3. Compare the pretty-printed outputs for exact equality
4. Include the PP options in the run manifest in the report

## Run Manifest

When using `--strict-pp`, the report includes a `run_manifest` section in the summary that documents the PP options used:

```json
{
  "summary": {
    "run_manifest": {
      "pretty_printer": {
        "method": "lean_delaborator",
        "options": {
          "pp.notation": "true",
          "pp.foralls": "true",
          "pp.parens": "true",
          "pp.unicode": "true",
          "pp.implicit": "false",
          "pp.explicit": "false"
        }
      }
    }
  }
}
```

This ensures that the exact PP configuration is recorded for reproducibility and auditing.

## Comparison with Python Normalization

The strict PP mode (Lean delaborator) differs from Python normalization (S0/S1) in several ways:

1. **Source of Truth**: Lean's delaborator uses Lean's internal representation, while Python normalization uses string manipulation.
2. **Notation Handling**: Lean's delaborator respects Lean's notation system, while Python normalization uses regex-based replacements.
3. **Determinism**: Both approaches aim for determinism, but Lean's delaborator is guaranteed to be consistent with Lean's type-checker.
4. **Performance**: Lean's delaborator requires running Lean for each proposition, which may be slower than Python normalization.

## Future Considerations

- **Additional PP Options**: We may consider adding more PP options (e.g., `pp.proofs`, `pp.proofs.withType`) if needed.
- **PP Option Profiles**: We may define multiple PP profiles for different use cases (e.g., a "verbose" profile with explicit types).
- **Lean Version Updates**: When updating Lean versions, we should test that PP behavior remains consistent or update the PP options accordingly.

## References

- [Lean 4 Pretty-Printing Documentation](https://leanprover-community.github.io/lean4-metaprogramming-book/extra/03_pretty-printing.html)
- [Lean 4 Delaborator Documentation](https://leanprover-community.github.io/lean4-metaprogramming-book/extra/03_pretty-printing.html#delaborators)
- [Lean 4 PP Options Reference](https://leanprover.github.io/lean4/doc/pretty.html)

