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
  "https://github.com/leanprover/std4" @ "d5471b83378e8ace4845f9a029af92f8b0cf10cb"
require Cli from git "https://github.com/mhuisi/lean4-cli" @ "nightly"
-- Megaparsec is not updated with recent lean4 version + apparently unmaintained
-- require Megaparsec from git
  -- "https://github.com/lurk-lab/Megaparsec.lean" @ "93b28d0ee4be435b6b395d8b6f816fabfc085166"
