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
  , typeuse := .elab_param_res [(.none, .num .i32), (.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , wasm_return
    ]
  }

/- string_sub : string × int × int → string -/
def string_sub : Module.Field := .funcs
  { lbl     := .some string_sub_id
  , typeuse := .elab_param_res [(.none, .num .i32), (.none, .num .i32), (.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , wasm_return
    ]
  }

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

#eval string_equal

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
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , wasm_return
    ]
  }

/- string_terminated : char[] × int → bool
   Checks that the char array is \0 terminated
 -/
def string_terminated : Module.Field := .funcs
  { lbl     := .some string_terminated_id
  , typeuse := .elab_param_res [(.none, .num .i32), (.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , wasm_return
    ]
  }

/- string_to_chararray : string → char[] -/
def string_to_chararray : Module.Field := .funcs
  { lbl     := .some string_to_chararray_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , wasm_return
    ]
  }

/- string_from_chararray : char[] → string -/
def string_from_chararray : Module.Field := .funcs
  { lbl     := .some string_from_chararray_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , wasm_return
    ]
  }

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
