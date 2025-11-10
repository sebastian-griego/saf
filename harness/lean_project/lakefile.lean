import Lake
open Lake DSL

package «saf» where

-- Frozen mathlib4 dependency for reproducible S0 normalization
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
  @ "5d2ad00e3ff6eb9d93b3c52370a308ee24d5dbe8"

@[default_target]
lean_lib SAF where
