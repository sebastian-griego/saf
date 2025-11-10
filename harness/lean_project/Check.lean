import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Divisibility.Basic

def _candidate : Prop :=
  forall a b : ℤ, a ∣ b -> exists k : ℤ, b = a * k

#check (_candidate : Prop)