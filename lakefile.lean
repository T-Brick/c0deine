import Lake
open Lake DSL

package c0deine {
  -- add package configuration options here
}

lean_lib C0deine {
  -- add library configuration options here
}

@[default_target]
lean_exe c0deine {
  root := `Main
}

require std from git "https://github.com/leanprover/std4" @ "main"
require Parser from git "https://github.com/fgdorais/lean4-parser" @ "main"
require Cli from git "https://github.com/mhuisi/lean4-cli" @ "nightly"
