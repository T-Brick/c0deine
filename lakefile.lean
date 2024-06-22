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

-- use argument "web" for non-local execution
lean_exe wasm_builder {
  root := `BuildWasm
}

script js (args : List String) do
  let out ← IO.Process.output {
    stdin  := .piped
    stdout := .piped
    stderr := .piped
    cmd    := "node"
    args   := (".lake/build/wasm/c0deine.js" :: args).toArray
  }
  IO.print out.stdout
  IO.print out.stderr
  return out.exitCode

-- require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.8.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"
require Cli from git "https://github.com/mhuisi/lean4-cli" @ "nightly"
require numbers from git "https://github.com/T-Brick/Numbers" @ "main"
require controlflow from git "https://github.com/T-Brick/ControlFlow" @ "main"
require wasm from git "https://github.com/T-Brick/lean-wasm" @ "main"

require importGraph from git "https://github.com/leanprover-community/import-graph" @ "v4.8.0"
