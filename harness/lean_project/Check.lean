import Mathlib.Data.Int.Basic

def _candidate : Prop :=
  ∀ a b : ℤ, a ≠ b ∧ a ≠ b

#check (_candidate : Prop)