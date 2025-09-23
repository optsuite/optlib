import Lake
open Lake DSL

package optlib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Optlib where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"

meta if get_config? env = some "CI_BUILD" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "c2156beadb1a4d049ff3b19fe396c5403025aac5"
