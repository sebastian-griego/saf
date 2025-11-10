import Mathlib.Data.Nat.Basic

def _candidate : Prop :=
  ∀ a b : ℕ, a ≥ b ∧ ∃ k, b + k = a

#check (_candidate : Prop)