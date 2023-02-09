import Lake
open Lake DSL

package «rSA-cryptosystems» {
  -- add package configuration options here
}
require mathlib from git
    "https://github.com/leanprover-community/mathlib4.git"

lean_lib «RSACryptosystems» {
  -- add library configuration options here
}

@[default_target]
lean_exe «rSA-cryptosystems» {
  root := `Main
}
