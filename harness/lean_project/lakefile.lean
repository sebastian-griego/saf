import Lake
open Lake DSL

package «saf» where

-- Minimal dependency on mathlib4. Pin a commit/branch for reproducibility if you like.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
  @ "master"

@[default_target]
lean_lib SAF where
