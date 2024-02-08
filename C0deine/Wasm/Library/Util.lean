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

/- takes int in local string_fromint.num and returns string_fromint.str -/
def string_fromint : List Instr := [wat_instr_list|
    block
      block
        local.get ↑num
        br_if 0           -- quick bound for when num == 0
        i32.const 2
        call ↑Label.calloc.toWasmIdent
        local.tee ↑str
        i32.const ↑(Unsigned.ofNat '0'.toNat)
        i32.store8
        br 1
      end
      local.get ↑num      -- record sign and flipping if needed
      local.get ↑num
      i32.const 0
      i32.lt_s
      local.tee ↑sign     -- 1 if negative, 0 if positive
      i32.const ↑(-1)
      i32.mul             -- now -1 if negative, 0 if positive
      i32.xor             -- num ^ (-sign) + sign = abs(num)
      local.get ↑sign
      i32.add
      local.set ↑num      -- num is now positive and sign is set
      i32.const 0
      local.set ↑len
      local.get ↑num
      local.set ↑n
      block               -- compute digit length of integers
        loop
          local.get ↑n
          i32.eqz
          br_if 1
          local.get ↑len
          i32.const 1
          i32.add
          local.set ↑len
          local.get ↑n
          i32.const 10
          i32.div_s
          local.set ↑n
          br 0
        end
      end
      local.get ↑len
      local.get ↑sign
      i32.const 1
      i32.add
      i32.add             -- add space for sign and \0
      call ↑Label.calloc.toWasmIdent
      local.tee ↑str
      local.tee ↑strw
      i32.const ↑(Unsigned.ofNat '-'.toNat)
      i32.store8          -- always add negative sign, just override it if pos
      local.get ↑strw
      local.get ↑sign
      i32.add
      local.get ↑len
      i32.add
      i32.const 1
      i32.sub
      local.set ↑strw     -- move strw to the end; decrement as we go
      i32.const 0
      local.set ↑n        -- n can be used as indexer now
      loop
        local.get ↑n
        local.get ↑len
        i32.ge_s
        br_if 1           -- done if n ≥ len
        local.get ↑strw
        local.get ↑num
        i32.const 10
        i32.rem_s
        i32.const ↑(Unsigned.ofNat '0'.toNat)
        i32.add
        i32.store8        -- store char
        local.get ↑num    -- update vars
        i32.const 10
        i32.div_s
        local.set ↑num
        local.get ↑strw
        i32.const 1
        i32.sub
        local.set ↑strw
        local.get ↑n
        i32.const 1
        i32.add
        local.set ↑n
        br 0
      end -- loop
    end
  ]
where
  num  : Ident := ⟨"num" , by decide, by decide⟩
  n    : Ident := ⟨"n"   , by decide, by decide⟩
  str  : Ident := ⟨"str" , by decide, by decide⟩
  strw : Ident := ⟨"strw", by decide, by decide⟩
  len  : Ident := ⟨"len" , by decide, by decide⟩
  sign : Ident := ⟨"sign", by decide, by decide⟩
  params : List Typ.Param := [⟨num, .num .i32⟩]
  locals : List Module.Local :=
    [ ⟨n, .num .i32⟩, ⟨str, .num .i32⟩, ⟨strw, .num .i32⟩, ⟨len, .num .i32⟩
    , ⟨sign, .num .i32⟩
    ]

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
