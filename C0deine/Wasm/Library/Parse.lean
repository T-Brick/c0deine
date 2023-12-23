/- C0deine - Parse
   WASM for C0's "parse" standard library.
   - Thea Brick
 -/
import C0deine.Wasm.Library.Util

namespace C0deine.Target.Wasm.Library.Parse

open Numbers C0deine.Target.Wasm Wasm.Text Wasm.Text.Instr
  Wasm.Syntax.Instr.Numeric Wasm.Syntax.Instr.Memory

def is_space_id      : Ident := ⟨"is_space"        , sorry, sorry⟩
def consume_space_id : Ident := ⟨"consume_space"   , sorry, sorry⟩
def take_int_id      : Ident := ⟨"take_int"        , sorry, sorry⟩

def parse_bool_id    : Ident := ⟨"parse_bool"  , sorry, sorry⟩
def parse_int_id     : Ident := ⟨"parse_int"   , sorry, sorry⟩
def num_tokens_id    : Ident := ⟨"num_tokens"  , sorry, sorry⟩
def int_tokens_id    : Ident := ⟨"int_tokens"  , sorry, sorry⟩
def parse_tokens_id  : Ident := ⟨"parse_tokens", sorry, sorry⟩
def parse_ints_id    : Ident := ⟨"parse_ints"  , sorry, sorry⟩

/- is_space : char → bool
   Checks whether a given char is a whitespace character
 -/
def is_space : Module.Field := .funcs
  { lbl     := .some is_space_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ block .no_label <|
      char 32     --    space
      ++ char 9   -- \t tab
      ++ char 10  -- \n linefeed
      ++ char 11  -- \v vertical tab
      ++ char 12  -- \f form feed
      ++ char 13  -- \r carriage return
      ++ [ i32_const 0
         , Plain.wasm_return
         ]
    , i32_const 1
    , Plain.wasm_return
    ]
  }
where char (n : Unsigned32) :=
  [ locl (.get 0)
  , i32_const n
  , i32_rel .eq
  , Plain.br_if 0
  ]

/- consume_space : string → string
   Returns the string without spaces in the front
 -/
def consume_space : Module.Field := .funcs
  { lbl     := .some consume_space_id
  , typeuse := .elab_param_res [(str, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    :=
    [ block .no_label       -- try consume spaces
      [ loop .no_label
        [ locl (.get str)
        , i32_mem (.load8 .u ⟨0, 0⟩)
        , i32_eqz
        , Plain.br_if 1     -- read a \0, end of string
        , locl (.get str)
        , i32_mem (.load8 .u ⟨0, 0⟩)
        , Plain.call is_space_id
        , i32_eqz
        , Plain.br_if 1     -- read a non-space
        , locl (.get str)
        , i32_const 1
        , i32_bin .add
        , locl (.set str)   -- increment string
        , Plain.br 0        -- repeat
        ]
      ]
    , locl (.get str)
    , Plain.wasm_return
    ]
  }
where 
  str : Ident := ⟨"str", sorry, sorry⟩

/- take_int: string × (base : int) → int* × string
   Tries to parse an integer from the string and returns the remainder when a
   whitespace character is reached.
 -/
def take_int : Module.Field := .funcs
  { lbl     := .some take_int_id
  , typeuse := .elab_param_res [(str, .num .i32), (base, .num .i32)] [.num .i32, .num .i32]
  , locals  := [⟨c, .num .i32⟩, ⟨res, .num .i32⟩, ⟨sign, .num .i32⟩]
  , body    :=
    [ block .no_label             -- check base is within bounds
      [ block .no_label
        [ locl (.get base)
        , i32_const 2
        , i32_rel (.lt .s)
        , Plain.br_if 0
        , locl (.get base)
        , i32_const 36
        , i32_rel (.gt .s)
        , Plain.br_if 0
        , Plain.br 1
        ]
      , Error.assert   -- todo maybe make this "error" with a specific msg
      , Plain.call Label.abort.toWasmIdent
      , Plain.unreachable
      ]
    , i32_const 0
    , locl (.set res)
    , block (.name fail)
      [ block .no_label
        [ i32_const 1
        , locl (.set sign)
        , block .no_label       -- first check for a negative sign
          [ locl (.get str)
          , i32_mem (.load8 .u ⟨0, 0⟩)
          , i32_const (Unsigned.ofNat '-'.toNat)
          , i32_rel .ne
          , Plain.br_if 0
          , i32_const (-1)
          , locl (.set sign)
          , locl (.get str)
          , i32_const 1
          , i32_bin .add
          , locl (.set str)     -- increment string if there is a '-'
          ]
        , loop (.name next) <|
          [ locl (.get str)
          , i32_mem (.load8 .u ⟨0, 0⟩)
          , locl (.tee c)
          , i32_eqz
          , Plain.br_if 1       -- if \0 then end of string
          , locl (.get c)
          , Plain.call is_space_id
          , Plain.br_if 1       -- encounted a whitespace char
          , locl (.get str)
          , i32_const 1
          , i32_bin .add
          , locl (.set str)     -- increment str pointer
          , locl (.get res)
          , locl (.get base)
          , i32_bin .mul
          , locl (.set res)     -- shift the number
          , locl (.get c)
          , i32_const (Unsigned.ofNat '0'.toNat)
          , i32_rel (.lt .u)
          , Plain.br_if fail
          , block .no_label
            [ locl (.get c)
            , i32_const (Unsigned.ofNat '9'.toNat)
            , i32_rel (.gt .u)
            , Plain.br_if 0
            , locl (.get c)     -- 0 ≤ c ≤ 9
            , i32_const (Unsigned.ofNat '0'.toNat)
            , i32_bin .sub
            , locl (.tee c)
            , locl (.get base)
            , i32_rel (.ge .u)
            , Plain.br_if fail  -- fail if c ≥ base
            , locl (.get res)
            , locl (.get c)
            , i32_bin .add
            , locl (.set res)
            , Plain.br next     -- successfully parsed digit
            ]
          , locl (.get c)       -- not a digit between 0-9 (c > '9')
          , i32_const (Unsigned.ofNat 'A'.toNat)
          , i32_rel (.lt .u)
          , Plain.br_if fail    -- fail if c < 'A'
          , block .no_label
            [ locl (.get c)
            , i32_const (Unsigned.ofNat 'Z'.toNat)
            , i32_rel (.gt .u)
            , Plain.br_if 0
            , locl (.get c)     -- 'A' ≤ c ≤ 'Z'
            , i32_const (Unsigned.ofNat 'A'.toNat - 10)
            , i32_bin .sub
            , locl (.tee c)
            , locl (.get base)
            , i32_rel (.ge .u)
            , Plain.br_if fail  -- fail if c ≥ base
            , locl (.get res)
            , locl (.get c)
            , i32_bin .add
            , locl (.set res)
            , Plain.br next     -- successfully parsed digit
            ]
          ] ++  -- for some reason type inference is failing me without append
          [ locl (.get c)       -- not a digit between 0-9 and A-Z
          , i32_const (Unsigned.ofNat 'a'.toNat)
          , i32_rel (.lt .u)
          , Plain.br_if fail    -- fail if c < 'a'
          , locl (.get c)
          , i32_const (Unsigned.ofNat 'z'.toNat)
          , i32_rel (.gt .u)
          , Plain.br_if fail    -- fail if c > 'z'
          , locl (.get c)       -- 'a' ≤ c ≤ 'z'
          , i32_const (Unsigned.ofNat 'a'.toNat - 10)
          , i32_bin .sub
          , locl (.tee c)
          , locl (.get base)
          , i32_rel (.ge .u)
          , Plain.br_if fail  -- fail if c ≥ base
          , locl (.get res)
          , locl (.get c)
          , i32_bin .add
          , locl (.set res)
          , Plain.br next     -- successfully parsed digit
          ]
        ]
      , i32_const 4
      , Plain.call Label.calloc.toWasmIdent
      , locl (.tee c)         -- save alloc'd pointer in c since it is unused
      , locl (.get res)
      , locl (.get sign)
      , i32_bin .mul          -- apply sign to res
      , i32_mem (.store ⟨0, 0⟩)
      , locl (.get c)
      , locl (.get str)
      , Plain.wasm_return
      ]
    , i32_const 0
    , locl (.get str)
    , Plain.wasm_return
    ]
  }
where
  str  : Ident := ⟨"str"  , sorry, sorry⟩
  base : Ident := ⟨"base" , sorry, sorry⟩
  c    : Ident := ⟨"c"    , sorry, sorry⟩
  res  : Ident := ⟨"res"  , sorry, sorry⟩
  sign : Ident := ⟨"sign" , sorry, sorry⟩
  next : Ident := ⟨"next" , sorry, sorry⟩
  fail : Ident := ⟨"fail" , sorry, sorry⟩

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
        [ locl (.get 0)
        , i32_mem (.load8 .u ⟨0, 0⟩)
        , i32_const (Unsigned.ofNat 't'.toNat)
        , i32_rel .ne
        , Plain.br_if 0 -- try parsing false
        , locl (.get 0)
        , i32_mem (.load8 .u ⟨1, 0⟩)
        , i32_const (Unsigned.ofNat 'r'.toNat)
        , i32_rel .ne
        , Plain.br_if 1
        , locl (.get 0)
        , i32_mem (.load8 .u ⟨2, 0⟩)
        , i32_const (Unsigned.ofNat 'u'.toNat)
        , i32_rel .ne
        , Plain.br_if 1
        , locl (.get 0)
        , i32_mem (.load8 .u ⟨3, 0⟩)
        , i32_const (Unsigned.ofNat 'e'.toNat)
        , i32_rel .ne
        , Plain.br_if 1
        , locl (.get 0)
        , i32_mem (.load8 .u ⟨4, 0⟩)
        , i32_const 0
        , i32_rel .ne
        , Plain.br_if 1
        , i32_const 1
        , Plain.call Label.calloc.toWasmIdent
        , locl (.tee 0)
        , i32_const 1
        , i32_mem (.store8 ⟨0, 0⟩)
        , locl (.get 0)
        , Plain.wasm_return
        ]
      , locl (.get 0)
      , i32_mem (.load8 .u ⟨0, 0⟩)
      , i32_const (Unsigned.ofNat 'f'.toNat)
      , i32_rel .ne
      , Plain.br_if 0 -- not a bool
      , locl (.get 0)
      , i32_mem (.load8 .u ⟨1, 0⟩)
      , i32_const (Unsigned.ofNat 'a'.toNat)
      , i32_rel .ne
      , Plain.br_if 0
      , locl (.get 0)
      , i32_mem (.load8 .u ⟨2, 0⟩)
      , i32_const (Unsigned.ofNat 'l'.toNat)
      , i32_rel .ne
      , Plain.br_if 0
      , locl (.get 0)
      , i32_mem (.load8 .u ⟨3, 0⟩)
      , i32_const (Unsigned.ofNat 's'.toNat)
      , i32_rel .ne
      , Plain.br_if 0
      , locl (.get 0)
      , i32_mem (.load8 .u ⟨4, 0⟩)
      , i32_const (Unsigned.ofNat 'e'.toNat)
      , i32_rel .ne
      , Plain.br_if 0
      , locl (.get 0)
      , i32_mem (.load8 .u ⟨5, 0⟩)
      , i32_const 0
      , i32_rel .ne
      , Plain.br_if 0
      , i32_const 1
      , Plain.call Label.calloc.toWasmIdent
      , locl (.tee 0)
      , i32_const 0
      , i32_mem (.store8 ⟨0, 0⟩)
      , locl (.get 0)
      , Plain.wasm_return
      ]
    , i32_const 0
    , Plain.wasm_return
    ]
  }

/- parse_int : string × (base : int) → bool*
   base must be between 2 and 36 returns pointer to int if could parse,
   otherwise NULL
 -/
def parse_int : Module.Field := .funcs
  { lbl     := .some parse_int_id
  , typeuse := .elab_param_res [(str, .num .i32), (base, .num .i32)] [.num .i32]
  , locals  := []
  , body    :=
    [ locl (.get str)
    , locl (.get base)
    , Plain.call take_int_id
    , locl (.set str)
    , locl (.set base)  -- pointer to int
    , block .no_label
      [ locl (.get str)
      , i32_mem (.load8 .u ⟨0, 0⟩)
      , i32_eqz
      , Plain.br_if 0
      , i32_const 0     -- ended on non-null char
      , Plain.wasm_return
      ]
    , locl (.get base)
    , Plain.wasm_return
    ]
  }
where
  str  : Ident := ⟨"str"  , sorry, sorry⟩
  base : Ident := ⟨"base" , sorry, sorry⟩

/- num_tokens : string → int -/
def num_tokens : Module.Field := .funcs
  { lbl     := .some num_tokens_id
  , typeuse := .elab_param_res [(str, .num .i32)] [.num .i32]
  , locals  := [⟨res, .num .i32⟩]
  , body    :=
    [ i32_const 0
    , locl (.set res)
    , block (.name done)
      [ loop (.name cont)
        [ locl (.get str)
        , Plain.call consume_space_id
        , locl (.tee str)
        , i32_mem (.load8 .u ⟨0, 0⟩)
        , i32_eqz
        , Plain.br_if done      -- at \0, end of string
        , locl (.get res)       -- increment total number seen
        , i32_const 1
        , i32_bin .add
        , locl (.set res)
        , loop .no_label        -- try and consume non-spaces
          [ locl (.get str)
          , i32_mem (.load8 .u ⟨0, 0⟩)
          , i32_eqz
          , Plain.br_if done    -- read a \0, end of string
          , locl (.get str)
          , i32_mem (.load8 .u ⟨0, 0⟩)
          , Plain.call is_space_id
          , Plain.br_if cont    -- read a space, start over
          , locl (.get str)
          , i32_const 1
          , i32_bin .add
          , locl (.set str)     -- increment string
          , Plain.br 0          -- repeat
          ]
        ]
      ]
    , locl (.get res)
    , Plain.wasm_return
    ]
  }
where
  str  : Ident := ⟨"str" , sorry, sorry⟩
  res  : Ident := ⟨"res" , sorry, sorry⟩
  done : Ident := ⟨"done", sorry, sorry⟩
  cont : Ident := ⟨"cont", sorry, sorry⟩

/- int_tokens : string × (base : int) → bool
   Returns true if the string is whitespace separated ints
 -/
def int_tokens : Module.Field := .funcs
  { lbl     := .some int_tokens_id
  , typeuse := .elab_param_res [(.none, .num .i32), (.none, .num .i32)] [.num .i32]
  , locals  := [⟨.some Temp.general.toWasmIdent, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , Plain.wasm_return
    ]
  }

/- parse_tokens : string → string[] -/
def parse_tokens : Module.Field := .funcs
  { lbl     := .some parse_tokens_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.some Temp.general.toWasmIdent, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , Plain.wasm_return
    ]
  }

/- parse_ints : string → int[] -/
def parse_ints : Module.Field := .funcs
  { lbl     := .some parse_ints_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.some Temp.general.toWasmIdent, .num .i32⟩]
  , body    :=
    [ .comment "todo impl"
    , i32_const 0
    , Plain.wasm_return
    ]
  }

def imports : List Module.Field := []
def extern : List Module.Field :=
  [ parse_bool
  , parse_int
  , num_tokens
  , int_tokens
  , parse_tokens
  , parse_ints
  ]
def intern : List Module.Field :=
  [ is_space
  , consume_space
  , take_int
  ]
def lib : List Module.Field := imports ++ intern ++ extern

end Parse

def Parse : Library :=
  { imports := Parse.imports
  , extern  := Parse.extern
  , intern  := Parse.intern
  , lib     := Parse.lib
  }
