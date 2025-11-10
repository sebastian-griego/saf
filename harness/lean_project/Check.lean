import Mathlib.Data.Nat.Basic

def _candidate : Prop :=
  ∀ a b : ℕ, a * b = b * a

#check (_candidate : Prop)