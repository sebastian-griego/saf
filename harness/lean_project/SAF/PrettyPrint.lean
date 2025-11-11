/-!
Pretty-printing utilities for deterministic output.

This module provides a command to pretty-print propositions with pinned
pretty-printer options for deterministic comparison in the strict tier.

PP Options Profile (strict tier):
- pp.notation = true (use notations like →, ↔, ∀, ∃)
- pp.foralls = true (show forall quantifiers explicitly)
- pp.parens = true (add parentheses where needed for clarity)
- pp.unicode = true (use Unicode characters)
- pp.implicit = false (hide implicit arguments)
- pp.explicit = false (hide explicit type annotations)

These options are set via `set_option` commands in the generated Lean scripts.
-/
