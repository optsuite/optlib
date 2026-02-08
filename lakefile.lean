import Lake
open Lake DSL

package «reaslib» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`weak.linter.mathlibStandardSet, true⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.24.0"

@[default_target]
lean_lib «Reaslib» where
