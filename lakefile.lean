import Lake
open Lake DSL

package «gtsmdn» where
  -- Add package configuration here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «GTSmdn» where
  -- Library configuration
  globs := #[.submodules `GTSmdn]
