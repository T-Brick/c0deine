import C0deine.X86.X86
import Wasm.Text.Module

namespace C0deine

inductive Target
| wasm
| x86
| c

namespace Wasm

inductive Config.Main
| start    -- calls imported `conio.println` with the result
| «import» -- user must define a `c0deine.main` function that calls `_c0_main`
| «return» -- the `main` function simply returns the result of `_c0_main`

structure Config where
  /- WASM allows users to define functions to be imported from external
      sources without having to be defined in the file.
  -/
  import_calloc : Bool
  import_abort  : Bool
  main          : Config.Main

instance : Inhabited Config where default :=
  { import_calloc := false
  , import_abort  := true
  , main          := .start
  }

end Wasm
