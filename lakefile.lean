import Lake
open Lake DSL

package «convex» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Analysis» {
  -- add any library configuration options here
}

lean_lib «Function» {
  -- add any library configuration options here
}

lean_lib «Algorithm» {
  -- add any library configuration options here
}

lean_lib «Example» {
  -- add any library configuration options here
}

lean_lib «Optimality» {
  -- add any library configuration options here
}
