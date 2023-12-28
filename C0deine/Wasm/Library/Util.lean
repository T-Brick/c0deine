/- C0deine - Util
   Utilities for the WASM implementation of the C0 Standard Libraries.
   - Thea Brick
 -/
import C0deine.Wasm.Wasm
import Wasm.Text.Module
import Wasm.Notation

namespace C0deine.Target.Wasm

open Numbers C0deine.Target.Wasm Wasm.Text Wasm.Text.Instr

structure Library where
  imports : List Module.Field
  extern  : List Module.Field
  intern  : List Module.Field
  lib     : List Module.Field

namespace Library.Util
-- todo should these just be a functions?

open Wasm.Text.Notation

def string_fromint : List Instr :=
  [ .comment "todo impl" ]

/- takes a bool in the zeroth local returns string in same local -/
def string_frombool : List Instr := [wat_instr_list|
    block
      block
        local.get 0
        br_if 0
        i32.const 6
        call ↑Label.calloc.toWasmIdent
        local.tee 0
        i32.const ↑(Unsigned.ofNat 'f'.toNat)
        i32.store8
        local.get 0
        i32.const ↑(Unsigned.ofNat 'a'.toNat)
        i32.store8 offset=1
        local.get 0
        i32.const ↑(Unsigned.ofNat 'l'.toNat)
        i32.store8 offset=2
        local.get 0
        i32.const ↑(Unsigned.ofNat 's'.toNat)
        i32.store8 offset=3
        local.get 0
        i32.const ↑(Unsigned.ofNat 'e'.toNat)
        i32.store8 offset=4
        br 1
      end
      i32.const 5   -- input is true
      call ↑Label.calloc.toWasmIdent
      local.tee 0
      i32.const ↑(Unsigned.ofNat 't'.toNat)
      i32.store8
      local.get 0
      i32.const ↑(Unsigned.ofNat 'r'.toNat)
      i32.store8 offset=1
      local.get 0
      i32.const ↑(Unsigned.ofNat 'u'.toNat)
      i32.store8 offset=2
      local.get 0
      i32.const ↑(Unsigned.ofNat 'e'.toNat)
      i32.store8 offset=3
    end
  ]

/- takes a char in the zeroth local returns string in first local
 -/
def string_fromchar : List Instr := [wat_instr_list|
    i32.const 2
    call ↑Label.calloc.toWasmIdent
    local.tee 1
    local.get 0
    i32.store8
  ]
