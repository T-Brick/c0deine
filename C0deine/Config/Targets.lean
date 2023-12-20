/- C0deine - Targets
   Target languages for c0deine as well as config settings for them.
   - Thea Brick
 -/
import C0deine.X86.X86
import Wasm.Text.Module

namespace C0deine

inductive Target
| wasm  -- web assembly binary format
| wat   -- web assembly text format
| x64
| c
| c0bc  -- c0 bytecode
deriving Repr
instance : Inhabited Target where default := .wat

def Target.toString : Target → String
  | .wasm => "wasm"
  | .wat  => "wat"
  | .x64  => "x86-64"
  | .c    => "c"
  | .c0bc => "c0bc"
instance : ToString Target := ⟨Target.toString⟩

def Target.ofString (t : String) : Option Target :=
  match t.toLower with
  | "x86" | "x64" | "x86-64" | "x86_64" | "amd64" | "intel64"
           => some .x64
  | "wasm" => some .wasm
  | "wat"  => some .wat
  | "c"    => some .c
  | "c0bc" => some .c0bc
  | _      => none

def Target.supported : List Target := [wasm, wat]
def Target.supported_str : String :=
  s!"Supported targets: '{"', '".intercalate (supported.map toString)}'"

def Target.isBinaryFormat : Target → Bool
  | .wasm => true
  | .wat  => false
  | .x64  => false
  | .c    => false
  | .c0bc => true -- is this correct?

def Target.isWasmFormat : Target → Bool
  | .wasm
  | .wat  => true
  | _     => false

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
