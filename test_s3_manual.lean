-- Simple propositional logic test
def _canonical : Prop := ∀ P Q : Prop, P → Q
def _candidate : Prop := ∀ P Q : Prop, ¬Q → ¬P

theorem _equiv : _canonical ↔ _candidate := by
  tauto

