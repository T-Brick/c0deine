/- C0deine - Parse
   WASM for C0's "parse" standard library.
   - Thea Brick
 -/
import C0deine.Wasm.Library.Util

namespace C0deine.Target.Wasm.Library.Parse

open Numbers C0deine.Target.Wasm Wasm.Text Wasm.Text.Instr
  Wasm.Syntax.Instr.Numeric Wasm.Syntax.Instr.Memory

def parse_bool_id   : Ident := ⟨"_c0_parse_bool"  , sorry, sorry⟩
def parse_int_id    : Ident := ⟨"_c0_parse_int"   , sorry, sorry⟩
def num_tokens_id   : Ident := ⟨"_c0_num_tokens"  , sorry, sorry⟩
def int_tokens_id   : Ident := ⟨"_c0_int_tokens"  , sorry, sorry⟩
def parse_tokens_id : Ident := ⟨"_c0_parse_tokens", sorry, sorry⟩
def parse_ints_id   : Ident := ⟨"_c0_parse_ints"  , sorry, sorry⟩

/- parse_bool : string → bool*
   returns pointer to bool if could parse, otherwise NULL
 -/
def parse_bool : Module.Field := .funcs
  { lbl     := .some parse_bool_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ block .no_label
      [ block .no_label
        [ locl (.get (.num 0))
        , i32_mem (.load8 .u ⟨0, 0⟩)
        , i32_const (Unsigned.ofNat 't'.toNat)
        , i32_rel .ne
        , Plain.br_if (.num 0) -- try parsing false
        , locl (.get (.num 0))
        , i32_mem (.load8 .u ⟨1, 0⟩)
        , i32_const (Unsigned.ofNat 'r'.toNat)
        , i32_rel .ne
        , Plain.br_if (.num 1)
        , locl (.get (.num 0))
        , i32_mem (.load8 .u ⟨2, 0⟩)
        , i32_const (Unsigned.ofNat 'u'.toNat)
        , i32_rel .ne
        , Plain.br_if (.num 1)
        , locl (.get (.num 0))
        , i32_mem (.load8 .u ⟨3, 0⟩)
        , i32_const (Unsigned.ofNat 'e'.toNat)
        , i32_rel .ne
        , Plain.br_if (.num 1)
        , locl (.get (.num 0))
        , i32_mem (.load8 .u ⟨4, 0⟩)
        , i32_const 0
        , i32_rel .ne
        , Plain.br_if (.num 1)
        , i32_const 1
        , Plain.call (.name Label.calloc.toWasmIdent)
        , locl (.tee (.num 0))
        , i32_const 1
        , i32_mem (.store8 ⟨0, 0⟩)
        , locl (.get (.num 0))
        , Plain.wasm_return
        ]
      , locl (.get (.num 0))
      , i32_mem (.load8 .u ⟨0, 0⟩)
      , i32_const (Unsigned.ofNat 'f'.toNat)
      , i32_rel .ne
      , Plain.br_if (.num 0) -- not a bool
      , locl (.get (.num 0))
      , i32_mem (.load8 .u ⟨1, 0⟩)
      , i32_const (Unsigned.ofNat 'a'.toNat)
      , i32_rel .ne
      , Plain.br_if (.num 0)
      , locl (.get (.num 0))
      , i32_mem (.load8 .u ⟨2, 0⟩)
      , i32_const (Unsigned.ofNat 'l'.toNat)
      , i32_rel .ne
      , Plain.br_if (.num 0)
      , locl (.get (.num 0))
      , i32_mem (.load8 .u ⟨3, 0⟩)
      , i32_const (Unsigned.ofNat 's'.toNat)
      , i32_rel .ne
      , Plain.br_if (.num 0)
      , locl (.get (.num 0))
      , i32_mem (.load8 .u ⟨4, 0⟩)
      , i32_const (Unsigned.ofNat 'e'.toNat)
      , i32_rel .ne
      , Plain.br_if (.num 0)
      , locl (.get (.num 0))
      , i32_mem (.load8 .u ⟨5, 0⟩)
      , i32_const 0
      , i32_rel .ne
      , Plain.br_if (.num 0)
      , i32_const 1
      , Plain.call (.name Label.calloc.toWasmIdent)
      , locl (.tee (.num 0))
      , i32_const 0
      , i32_mem (.store8 ⟨0, 0⟩)
      , locl (.get (.num 0))
      , Plain.wasm_return
      ]
    , i32_const 0
    , Plain.wasm_return
    ]
  }

/- parse_int : string × (base : int) → bool*
   base must be between 2 and 36
   returns pointer to int if could parse, otherwise NULL
 -/
def parse_int : Module.Field := .funcs
  { lbl     := .some parse_int_id
  , typeuse := .elab_param_res [(.none, .num .i32), (.none, .num .i32)] [.num .i32]
  , locals  := [⟨.some Temp.general.toWasmIdent, .num .i32⟩]
  , body    :=
    [ sorry
    ]
  }

/- num_tokens : string → int -/
def num_tokens : Module.Field := .funcs
  { lbl     := .some num_tokens_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.some Temp.general.toWasmIdent, .num .i32⟩]
  , body    :=
    [ sorry
    ]
  }

/- int_tokens : string × (base : int) → bool -/
def int_tokens : Module.Field := .funcs
  { lbl     := .some int_tokens_id
  , typeuse := .elab_param_res [(.none, .num .i32), (.none, .num .i32)] [.num .i32]
  , locals  := [⟨.some Temp.general.toWasmIdent, .num .i32⟩]
  , body    :=
    [ sorry
    ]
  }

/- parse_tokens : string → string[] -/
def parse_tokens : Module.Field := .funcs
  { lbl     := .some parse_tokens_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.some Temp.general.toWasmIdent, .num .i32⟩]
  , body    :=
    [ sorry
    ]
  }

/- parse_ints : string → int[] -/
def parse_ints : Module.Field := .funcs
  { lbl     := .some parse_ints_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.some Temp.general.toWasmIdent, .num .i32⟩]
  , body    :=
    [ sorry
    ]
  }

def imports : List Module.Field := []
def impls : List Module.Field :=
  [ parse_bool
  , parse_int
  , num_tokens
  , int_tokens
  , parse_tokens
  , parse_ints
  ]
def lib : List Module.Field :=
  imports ++ impls

end Parse

def Parse : Library :=
  { imports := Parse.imports
  , impls   := Parse.impls
  , lib     := Parse.lib
  }
