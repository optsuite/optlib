import Lake
open Lake DSL

package «convex» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Convex» {
}

meta if get_config? env = some "CI_BUILD" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "d1be57c7fbd80ac20584ed0a86a2165c62cd993b"
