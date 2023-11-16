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

require std from git
  "https://github.com/leanprover/std4" @ "v4.3.0-rc1"
require Cli from git "https://github.com/mhuisi/lean4-cli" @ "nightly"
require numbers from git
  "https://github.com/T-Brick/Numbers" @ "main"
-- Megaparsec is not updated with recent lean4 version + apparently unmaintained
require Megaparsec from git
  "https://github.com/lurk-lab/Megaparsec.lean" @ "main"
