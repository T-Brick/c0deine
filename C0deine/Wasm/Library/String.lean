/- C0deine - String
   WASM for C0's "string" standard library. Currently, `format` is not
   implemented since that requires variadic functions.
   - Thea Brick
 -/
import C0deine.Wasm.Library.Util
import Wasm.Notation

namespace C0deine.Target.Wasm.Library.String

open Numbers C0deine.Target.Wasm Wasm.Text Wasm.Text.Instr
  Wasm.Syntax.Instr.Numeric Wasm.Syntax.Instr.Memory

def string_length_id         : Ident := ⟨"string_length"        , sorry, sorry⟩
def string_charat_id         : Ident := ⟨"string_charat"        , sorry, sorry⟩
def string_join_id           : Ident := ⟨"string_join"          , sorry, sorry⟩
def string_sub_id            : Ident := ⟨"string_sub"           , sorry, sorry⟩
def string_equal_id          : Ident := ⟨"string_equal"         , sorry, sorry⟩
def string_compare_id        : Ident := ⟨"string_compare"       , sorry, sorry⟩
def string_fromint_id        : Ident := ⟨"string_fromint"       , sorry, sorry⟩
def string_frombool_id       : Ident := ⟨"string_frombool"      , sorry, sorry⟩
def string_fromchar_id       : Ident := ⟨"string_fromchar"      , sorry, sorry⟩
def string_tolower_id        : Ident := ⟨"string_tolower"       , sorry, sorry⟩
def string_terminated_id     : Ident := ⟨"string_terminated"    , sorry, sorry⟩
def string_to_chararray_id   : Ident := ⟨"string_to_chararray"  , sorry, sorry⟩
def string_from_chararray_id : Ident := ⟨"string_from_chararray", sorry, sorry⟩
def char_ord_id              : Ident := ⟨"char_ord"             , sorry, sorry⟩
def char_chr_id              : Ident := ⟨"char_chr"             , sorry, sorry⟩
def format_id                : Ident := ⟨"format"               , sorry, sorry⟩

open Wasm.Text.Notation

/- string_length : string → int -/
def string_length : Module.Field := .funcs
  { lbl     := .some string_length_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := [wat_instr_list|
      i32.const 0
      local.set 1
      block
        loop
          local.get 0
          local.get 1
          i32.add
          i32.load8_u
          i32.eqz
          br_if 1
          local.get 1
          i32.const 1
          i32.add
          local.set 1
          br 0
        end
      end
      local.get 1
      return
    ]
  }

/- string_charat : (s : string) × (idx : int) → char
   Return s[idx]; abort if out of bounds
 -/
def string_charat : Module.Field := .funcs
  { lbl     := .some string_charat_id
  , typeuse := .elab_param_res [(str, .num .i32), (idx, .num .i32)] [.num .i32]
  , locals  := []
  , body    := [wat_instr_list|
      block
        block
          local.get ↑idx
          i32.const 0
          i32.lt_s
          br_if 0
          local.get ↑idx
          local.get ↑str
          call ↑string_length_id
          i32.lt_s
          br_if 1
        end
        (↑Error.assert)
        call ↑Label.abort.toWasmIdent
        unreachable
      end
      local.get ↑str
      local.get ↑idx
      i32.add
      i32.load8_u
      return
    ]
  }
where
  str : Ident := ⟨"str", sorry, sorry⟩
  idx : Ident := ⟨"idx", sorry, sorry⟩

/- string_join : string × string → string -/
def string_join : Module.Field := .funcs
  { lbl     := .some string_join_id
  , typeuse := .elab_param_res [(str1, .num .i32), (str2, .num .i32)] [.num .i32]
  , locals  := [⟨str3, .num .i32⟩, ⟨len1, .num .i32⟩, ⟨len2, .num .i32⟩]
  , body    := [wat_instr_list|
      local.get ↑str1
      call ↑string_length_id
      local.tee ↑len1
      local.get ↑str2
      call ↑string_length_id
      local.tee ↑len2
      i32.const 1
      i32.add
      i32.add
      call ↑Label.calloc.toWasmIdent
      local.tee ↑str3
      local.get ↑str1
      local.get ↑len1
      memory.copy
      local.get ↑str3
      local.get ↑len1
      i32.add
      local.get ↑str2
      local.get ↑len2
      memory.copy
      local.get ↑str3
      return
    ]
  }
where
  str1 : Ident := ⟨"str1", sorry, sorry⟩
  str2 : Ident := ⟨"str2", sorry, sorry⟩
  str3 : Ident := ⟨"str3", sorry, sorry⟩
  len1 : Ident := ⟨"len1", sorry, sorry⟩
  len2 : Ident := ⟨"len2", sorry, sorry⟩

/- string_sub : string × int × int → string -/
def string_sub : Module.Field := .funcs
  { lbl     := .some string_sub_id
  , typeuse := .elab_param_res [(str, .num .i32), (start, .num .i32), (finish, .num .i32)] [.num .i32]
  , locals  := [⟨temp, .num .i32⟩]
  , body    := [wat_instr_list|
      local.get ↑finish
      local.get ↑start
      i32.sub
      local.set ↑temp
      block           -- bounds check
        block
          local.get ↑start
          i32.const 0
          i32.lt_s
          br_if 0
          local.get ↑temp
          i32.const 0
          i32.lt_s
          br_if 0     -- negative length
          local.get ↑str
          call ↑string_length_id
          -- local.tee ↑len
          local.get ↑finish
          i32.lt_s
          br_if 0
          br 1
        end
        (↑Error.assert)
        call ↑Label.abort.toWasmIdent
        unreachable
      end
      local.get ↑temp
      i32.const 1
      i32.add
      call ↑Label.calloc.toWasmIdent
      local.tee ↑finish       -- don't need finish anymore so store res in it
      local.get ↑str
      local.get ↑start
      i32.add
      local.get ↑temp
      memory.copy
      local.get ↑finish
      return
    ]
  }
where
  str    : Ident := ⟨"str", sorry, sorry⟩
  start  : Ident := ⟨"start", sorry, sorry⟩
  finish : Ident := ⟨"finish", sorry, sorry⟩
  temp   : Ident := ⟨"temp", sorry, sorry⟩

/- string_equal : string × string → bool -/
def string_equal : Module.Field := .funcs
  { lbl     := .some string_equal_id
  , typeuse := .elab_param_res [(str1, .num .i32), (str2, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := [wat_instr_list|
      block
        loop
          local.get ↑str1
          i32.load8_u
          local.get ↑str2
          i32.load8_u
          i32.ne
          br_if 1             -- strings are not equal
          local.get ↑str1
          i32.load8_u
          local.get ↑str2
          i32.load8_u
          i32.and             -- if either str1 or str2 NULL then 0
          local.get ↑str1
          i32.const 1
          i32.add
          local.set ↑str1     -- increment str1
          local.get ↑str2
          i32.const 1
          i32.add
          local.set ↑str2     -- increment str2
          br_if 0             -- restart loop if not null
        end
        i32.const 1
        return
      end
      i32.const 0
      return
    ]
  }
where
  str1 : Ident := ⟨"str1", sorry, sorry⟩
  str2 : Ident := ⟨"str2", sorry, sorry⟩

/- string_compare : string × string → int -/
def string_compare : Module.Field := .funcs
  { lbl     := .some string_compare_id
  , typeuse := .elab_param_res [(str1, .num .i32), (str2, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := [wat_instr_list|
      block
        loop
          local.get ↑str1
          i32.load8_u
          local.get ↑str2
          i32.load8_u
          i32.ne
          br_if 1           -- strings are not equal
          local.get ↑str1
          i32.load8_u
          local.get ↑str2
          i32.load8_u
          i32.and           -- if either str1 or str2 NULL then 0
          local.get ↑str1
          i32.const 1
          i32.add
          local.set ↑str1   -- increment str1
          local.get ↑str2
          i32.const 1
          i32.add
          local.set ↑str2   -- increment str2
          br_if 0           -- restart loop if not null
        end
        i32.const 0         -- equal
        return
      end
      block
        local.get ↑str1
        i32.load8_u
        local.get ↑str2
        i32.load8_u
        i32.lt_u
        br_if 0
        i32.const ↑(-1)     -- todo fix <<<<<<<<<<<<<<<<<<<<<<
        return
      end
      i32.const 1
      return
    ]
  }
where
  str1 : Ident := ⟨"str1", sorry, sorry⟩
  str2 : Ident := ⟨"str2", sorry, sorry⟩

/- string_fromint : int → string -/
def string_fromint : Module.Field := .funcs
  { lbl     := .some string_fromint_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := Util.string_fromint ++
    [ locl (.get 0)
    , wasm_return
    ]
  }

/- string_frombool : bool → string -/
def string_frombool : Module.Field := .funcs
  { lbl     := .some string_frombool_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := Util.string_frombool ++
    [ locl (.get 0)
    , wasm_return
    ]
  }

/- string_fromchar : char → string -/
def string_fromchar : Module.Field := .funcs
  { lbl     := .some string_fromchar_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := Util.string_fromchar ++
    [ locl (.get 1)
    , wasm_return
    ]
  }

/- string_tolower : string → string -/
def string_tolower : Module.Field := .funcs
  { lbl     := .some string_tolower_id
  , typeuse := .elab_param_res [(str, .num .i32)] [.num .i32]
  , locals  := [⟨temp, .num .i32⟩, ⟨str2, .num .i32⟩]
  , body    := [wat_instr_list|
      local.get ↑str
      call ↑string_length_id
      i32.const 1
      i32.add
      local.tee ↑temp
      call ↑Label.calloc.toWasmIdent
      local.tee ↑str2
      local.get ↑str
      local.get ↑temp         -- copy str into str2
      memory.copy
      local.get ↑str2
      local.set ↑str          -- dont need str1 anymore, store starter pointer
      block
        loop
          local.get ↑str2
          i32.load8_u
          local.tee ↑temp
          i32.eqz
          br_if 1             -- reached end of string
          local.get ↑str2
          i32.const 1
          i32.add
          local.set ↑str2     -- increment str2
          local.get ↑temp
          i32.const ↑(Unsigned.ofNat 'A'.toNat)
          i32.lt_u
          br_if 0             -- less than 'A' skip to next char
          local.get ↑temp
          i32.const ↑(Unsigned.ofNat 'Z'.toNat)
          i32.gt_u
          br_if 0             -- greater than 'Z' skip to next char
          local.get ↑str2
          i32.const 1
          i32.sub             -- go back to current char
          local.get ↑temp
          i32.const 32
          i32.add             -- add 32 to reacher lowercase characters
          i32.store8
          br 0
        end
      end
      local.get ↑str
      return
    ]
  }
where
  temp : Ident := ⟨"temp", sorry, sorry⟩
  str  : Ident := ⟨"str", sorry, sorry⟩
  str2 : Ident := ⟨"str2", sorry, sorry⟩

/- string_terminated : char[] × int → bool
   Checks that the char array is \0 terminated
 -/
def string_terminated : Module.Field := .funcs
  { lbl     := .some string_terminated_id
  , typeuse := .elab_param_res [(arr, .num .i32), (n, .num .i32)] [.num .i32]
  , locals  := [⟨i, .num .i32⟩]
  , body    := [wat_instr_list|
      block     -- bounds check
        block
          local.get ↑n
          i32.const 0
          i32.lt_s
          br_if 0
          local.get ↑arr
          i32.eqz
          br_if 0
          local.get ↑arr
          i32.const 8
          i32.sub         -- get array length
          i32.load
          local.get ↑n
          i32.lt_s
          br_if 0
          br 1
        end
        (↑Error.assert)
        call ↑Label.abort.toWasmIdent
        unreachable
      end
      i32.const 0
      local.set ↑i
      block ↑fail
        block ↑succ
          loop
            local.get ↑i
            local.get ↑n
            i32.ge_s
            br_if ↑fail
            local.get ↑arr
            local.get ↑i
            i32.add
            i32.load8_u
            i32.eqz
            br_if ↑succ
            local.get ↑i
            i32.const 1
            i32.add
            local.set ↑i
            br 0
          end
        end ↑succ
        i32.const 1
        return
      end ↑fail
      i32.const 0
      return
    ]
  }
where
  arr  : Ident := ⟨"arr", sorry, sorry⟩
  n    : Ident := ⟨"n", sorry, sorry⟩
  i    : Ident := ⟨"i", sorry, sorry⟩
  fail : Ident := ⟨"fail", sorry, sorry⟩
  succ : Ident := ⟨"succ", sorry, sorry⟩

/- string_to_chararray : string → char[] -/
def string_to_chararray : Module.Field := .funcs
  { lbl     := .some string_to_chararray_id
  , typeuse := .elab_param_res [(str, .num .i32)] [.num .i32]
  , locals  := [⟨arr, .num .i32⟩, ⟨temp, .num .i32⟩, ⟨arrw, .num .i32⟩]
  , body    := [wat_instr_list|
      local.get ↑str
      call ↑string_length_id
      i32.const 1
      i32.add                 -- 1 for \0
      local.tee ↑temp
      i32.const 8             -- 8 for length info
      i32.add
      call ↑Label.calloc.toWasmIdent
      local.tee ↑arr
      local.get ↑temp
      i32.store
      local.get ↑arr
      i32.const 8
      i32.add
      local.tee ↑arr
      local.set ↑arrw
      block
        loop
          local.get ↑str
          i32.load8_u
          local.tee ↑temp
          i32.eqz
          br_if 1           -- reached \0, done
          local.get ↑arrw
          local.get ↑temp
          i32.store8
          local.get ↑arrw
          i32.const 1
          i32.add
          local.set ↑arrw
          local.get ↑str
          i32.const 1
          i32.add
          local.set ↑str
          br 0
        end
      end
      local.get ↑arr
      return
    ]
  }
where
  str  : Ident := ⟨"str", sorry, sorry⟩
  arr  : Ident := ⟨"arr", sorry, sorry⟩
  temp : Ident := ⟨"temp", sorry, sorry⟩
  arrw : Ident := ⟨"arrw", sorry, sorry⟩

/- string_from_chararray : char[] → string -/
def string_from_chararray : Module.Field := .funcs
  { lbl     := .some string_from_chararray_id
  , typeuse := .elab_param_res [(arr, .num .i32)] [.num .i32]
  , locals  := [⟨str, .num .i32⟩, ⟨strw, .num .i32⟩, ⟨temp, .num .i32⟩]
  , body    := [wat_instr_list|
      block       -- contract checks
        block
          local.get ↑arr
          i32.eqz
          br_if 0
          local.get ↑arr
          local.get ↑arr
          i32.const 8
          i32.sub
          i32.load
          local.tee ↑str      -- store length here
          call ↑string_terminated_id
          br_if 1
        end
        (↑Error.assert)
        call ↑Label.abort.toWasmIdent
        unreachable
      end
      local.get ↑str
      call ↑Label.calloc.toWasmIdent
      local.tee ↑str
      local.set ↑strw
      block
        loop
          local.get ↑arr
          i32.load8_u
          local.tee ↑temp
          i32.eqz
          br_if 1
          local.get ↑strw
          local.get ↑temp
          i32.store8
          local.get ↑arr
          i32.const 1
          i32.add
          local.set ↑arr
          local.get ↑strw
          i32.const 1
          i32.add
          local.set ↑strw
          br 0
        end
      end
      local.get ↑str
      return
    ]
  }
where
  str  : Ident := ⟨"str", sorry, sorry⟩
  arr  : Ident := ⟨"arr", sorry, sorry⟩
  temp : Ident := ⟨"temp", sorry, sorry⟩
  strw : Ident := ⟨"strw", sorry, sorry⟩

/- char_ord : char → int -/
def char_ord : Module.Field := .funcs
  { lbl     := .some char_ord_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := []
  , body    :=
    [ locl (.get 0)
    , wasm_return
    ]
  }

/- char_chr : int → char -/
def char_chr : Module.Field := .funcs
  { lbl     := .some char_chr_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ locl (.get 0)
    , wasm_return
    ]
  }

/- format : string × ...args → string -/
def format : Module.Field := .funcs
  { lbl     := .some format_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , wasm_return
    ]
  }

def imports : List Module.Field := []
def «extern» : List Module.Field :=
  [ string_length
  , string_charat
  , string_join
  , string_sub
  , string_equal
  , string_compare
  , string_fromint
  , string_frombool
  , string_fromchar
  , string_tolower
  , string_terminated
  , string_to_chararray
  , string_from_chararray
  , char_ord
  , char_chr
  -- , format
  ]
def intern : List Module.Field := []
def lib    : List Module.Field := imports ++ intern ++ «extern»

end String

def String : Library :=
  { imports := String.imports
  , extern  := String.extern
  , intern  := String.intern
  , lib     := String.lib
  }
