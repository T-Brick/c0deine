/- C0deine - String
   WASM for C0's "string" standard library. Currently, `format` is not
   implemented since that requires variadic functions.
   - Thea Brick
 -/
import C0deine.Wasm.Library.Util

namespace C0deine.Target.Wasm.Library.String

open Numbers C0deine.Target.Wasm Wasm.Text Wasm.Text.Instr
  Wasm.Syntax.Instr.Numeric Wasm.Syntax.Instr.Memory

def string_length_id         : Ident := ⟨"_c0_string_length"        , sorry, sorry⟩
def string_charat_id         : Ident := ⟨"_c0_string_charat"        , sorry, sorry⟩
def string_join_id           : Ident := ⟨"_c0_string_join"          , sorry, sorry⟩
def string_sub_id            : Ident := ⟨"_c0_string_sub"           , sorry, sorry⟩
def string_equal_id          : Ident := ⟨"_c0_string_equal"         , sorry, sorry⟩
def string_compare_id        : Ident := ⟨"_c0_string_compare"       , sorry, sorry⟩
def string_fromint_id        : Ident := ⟨"_c0_string_fromint"       , sorry, sorry⟩
def string_frombool_id       : Ident := ⟨"_c0_string_frombool"      , sorry, sorry⟩
def string_fromchar_id       : Ident := ⟨"_c0_string_fromchar"      , sorry, sorry⟩
def string_tolower_id        : Ident := ⟨"_c0_string_tolower"       , sorry, sorry⟩
def string_terminated_id     : Ident := ⟨"_c0_string_terminated"    , sorry, sorry⟩
def string_to_chararray_id   : Ident := ⟨"_c0_string_to_chararray"  , sorry, sorry⟩
def string_from_chararray_id : Ident := ⟨"_c0_string_from_chararray", sorry, sorry⟩
def char_ord_id              : Ident := ⟨"_c0_char_ord"             , sorry, sorry⟩
def char_chr_id              : Ident := ⟨"_c0_char_chr"             , sorry, sorry⟩
def format_id                : Ident := ⟨"_c0_format"               , sorry, sorry⟩

/- string_length : string → int -/
def string_length : Module.Field := .funcs
  { lbl     := .some string_length_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ i32_const 0
    , locl (.set 0)
    , block .no_label
      [ loop .no_label
        [ locl (.get 0)
        , locl (.get 1)
        , i32_bin .add
        , i32_mem (.load8 .u ⟨0, 0⟩)
        , i32_eqz
        , Plain.br_if 1
        , locl (.get 1)
        , i32_const 1
        , i32_bin .add
        , locl (.set 1)
        , Plain.br 0
        ]
      ]
    , locl (.get 0)
    , Plain.wasm_return
    ]
  }

/- string_charat : (s : string) × (idx : int) → char
   Return s[idx]; abort if out of bounds
 -/
def string_charat : Module.Field := .funcs
  { lbl     := .some string_charat_id
  , typeuse := .elab_param_res [(.none, .num .i32), (.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ block .no_label
      [ block .no_label
        [ locl (.get 1)
        , locl (.get 1)
        , i32_const 0
        , i32_rel (.lt .s)
        , Plain.br_if 0
        , locl (.get 0)
        , Plain.call string_length_id
        , i32_rel (.lt .s)
        , Plain.br 1
        ]
      , Error.mem
      , Plain.call Label.abort.toWasmIdent
      , Plain.unreachable
      ]
    , locl (.get 0)
    , locl (.get 1)
    , i32_bin .add
    , i32_mem (.load8 .u ⟨0, 0⟩)
    , Plain.wasm_return
    ]
  }

/- string_join : string × string → string -/
def string_join : Module.Field := .funcs
  { lbl     := .some string_join_id
  , typeuse := .elab_param_res [(.none, .num .i32), (.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , Plain.wasm_return
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
    , Plain.wasm_return
    ]
  }

/- string_equal : string × string → bool -/
def string_equal : Module.Field := .funcs
  { lbl     := .some string_equal_id
  , typeuse := .elab_param_res [(.none, .num .i32), (.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , Plain.wasm_return
    ]
  }

/- string_compare : string × string → int -/
def string_compare : Module.Field := .funcs
  { lbl     := .some string_compare_id
  , typeuse := .elab_param_res [(.none, .num .i32), (.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , Plain.wasm_return
    ]
  }

/- string_fromint : int → string -/
def string_fromint : Module.Field := .funcs
  { lbl     := .some string_fromint_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := Util.string_fromint ++
    [ locl (.get 0)
    , Plain.wasm_return
    ]
  }

/- string_frombool : bool → string -/
def string_frombool : Module.Field := .funcs
  { lbl     := .some string_frombool_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := Util.string_frombool ++
    [ locl (.get 0)
    , Plain.wasm_return
    ]
  }

/- string_fromchar : char → string -/
def string_fromchar : Module.Field := .funcs
  { lbl     := .some string_fromchar_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := Util.string_fromchar ++
    [ locl (.get 1)
    , Plain.wasm_return
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
    , Plain.wasm_return
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
    , Plain.wasm_return
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
    , Plain.wasm_return
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
    , Plain.wasm_return
    ]
  }

/- char_ord : char → int -/
def char_ord : Module.Field := .funcs
  { lbl     := .some char_ord_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := []
  , body    :=
    [ locl (.get 0)
    , Plain.wasm_return
    ]
  }

/- char_chr : int → char -/
def char_chr : Module.Field := .funcs
  { lbl     := .some char_chr_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ locl (.get 0)
    , Plain.wasm_return
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
    , Plain.wasm_return
    ]
  }

def imports : List Module.Field := []
def impls : List Module.Field :=
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
def lib : List Module.Field :=
  imports ++ impls

end String

def String : Library :=
  { imports := String.imports
  , impls   := String.impls
  , lib     := String.lib
  }
