/- C0deine - Util
   Utilities for the WASM implementation of the C0 Standard Libraries.
   - Thea Brick
 -/
import C0deine.Wasm.Wasm
import Wasm.Text.Module

namespace C0deine.Target.Wasm

open Numbers C0deine.Target.Wasm Wasm.Text Wasm.Text.Instr

structure Library where
  imports : List Module.Field
  extern  : List Module.Field
  intern  : List Module.Field
  lib     : List Module.Field

namespace Library.Util
-- todo should these just be a functions?

def string_fromint : List Instr :=
  [ .comment "todo impl" ]

/- takes a bool in the zeroth local returns string in same local -/
def string_frombool : List Instr :=
  [ block .no_label
      [ block .no_label
        [ locl (.get 0)
        , br_if 0
        , i32_const 6
        , call Label.calloc.toWasmIdent
        , locl (.tee 0)
        , i32_const (Unsigned.ofNat 'f'.toNat)
        , i32_mem (.store8 ⟨0, 0⟩)
        , locl (.get 0)
        , i32_const (Unsigned.ofNat 'a'.toNat)
        , i32_mem (.store8 ⟨1, 0⟩)
        , locl (.get 0)
        , i32_const (Unsigned.ofNat 'l'.toNat)
        , i32_mem (.store8 ⟨2, 0⟩)
        , locl (.get 0)
        , i32_const (Unsigned.ofNat 's'.toNat)
        , i32_mem (.store8 ⟨3, 0⟩)
        , locl (.get 0)
        , i32_const (Unsigned.ofNat 'e'.toNat)
        , i32_mem (.store8 ⟨4, 0⟩)
        , br 1
        ]
      , i32_const 5           -- input is true
      , call Label.calloc.toWasmIdent
      , locl (.tee 0)
      , i32_const (Unsigned.ofNat 't'.toNat)
      , i32_mem (.store8 ⟨0, 0⟩)
      , locl (.get 0)
      , i32_const (Unsigned.ofNat 'r'.toNat)
      , i32_mem (.store8 ⟨1, 0⟩)
      , locl (.get 0)
      , i32_const (Unsigned.ofNat 'u'.toNat)
      , i32_mem (.store8 ⟨2, 0⟩)
      , locl (.get 0)
      , i32_const (Unsigned.ofNat 'e'.toNat)
      , i32_mem (.store8 ⟨3, 0⟩)
      ]
  ]

/- takes a char in the zeroth local returns string in first local
 -/
def string_fromchar : List Instr :=
  [ i32_const 2
  , call Label.calloc.toWasmIdent
  , locl (.tee 1)
  , locl (.get 0)
  , i32_mem (.store8 ⟨0, 0⟩)
  ]
