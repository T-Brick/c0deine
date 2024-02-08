/- C0deine - Parse
   WASM for C0's "parse" standard library.
   - Thea Brick
 -/
import C0deine.Wasm.Library.Util
import Wasm.Notation

namespace C0deine.Target.Wasm.Library.Parse

open Numbers C0deine.Target.Wasm Wasm.Text Wasm.Text.Instr
  Wasm.Syntax.Instr.Numeric Wasm.Syntax.Instr.Memory

def is_space_id      : Ident := ⟨"is_space"     , by decide, by decide⟩
def consume_space_id : Ident := ⟨"consume_space", by decide, by decide⟩
def take_int_id      : Ident := ⟨"take_int"     , by decide, by decide⟩

def parse_bool_id    : Ident := ⟨"parse_bool"   , by decide, by decide⟩
def parse_int_id     : Ident := ⟨"parse_int"    , by decide, by decide⟩
def num_tokens_id    : Ident := ⟨"num_tokens"   , by decide, by decide⟩
def int_tokens_id    : Ident := ⟨"int_tokens"   , by decide, by decide⟩
def parse_tokens_id  : Ident := ⟨"parse_tokens" , by decide, by decide⟩
def parse_ints_id    : Ident := ⟨"parse_ints"   , by decide, by decide⟩

-- todo consider way to embed lists of instrs like in `is_space`
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
         , wasm_return
         ]
    , i32_const 1
    , wasm_return
    ]
  }
where char (n : Unsigned32) :=
  [ locl (.get 0)
  , i32_const n
  , i32_rel .eq
  , br_if 0
  ]

open Wasm.Text.Notation

/- consume_space : string → string
   Returns the string without spaces in the front
 -/
def consume_space : Module.Field := .funcs
  { lbl     := .some consume_space_id
  , typeuse := .elab_param_res [(str, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := [wat_instr_list|
      block               -- try consume spaces
        loop
          local.get ↑str
          i32.load8_u
          i32.eqz
          br_if 1         -- read a \0, end of string
          local.get ↑str
          i32.load8_u
          call ↑is_space_id
          i32.eqz
          br_if 1         -- read a non-space
          local.get ↑str
          i32.const 1
          i32.add
          local.set ↑str  -- increment string
          br 0            -- repeat
        end
      end
      local.get ↑str
      return
    ]
  }
where
  str : Ident := ⟨"str", by decide, by decide⟩

/- take_int: string × (base : int) → bool × int × string
   Tries to parse an integer from the string and returns the remainder when a
   whitespace character is reached.
 -/
def take_int : Module.Field := .funcs
  { lbl     := .some take_int_id
  , typeuse := .elab_param_res [(str, .num .i32), (base, .num .i32)]
                  [.num .i32, .num .i32, .num .i32]
  , locals  := [⟨c, .num .i32⟩, ⟨res, .num .i32⟩, ⟨sign, .num .i32⟩]
  , body    := [wat_instr_list|
      block                       -- check base is within bounds
        block
          local.get ↑base
          i32.const 2
          i32.lt_s
          br_if 0
          local.get ↑base
          i32.const 36
          i32.gt_s
          br_if 0
          br 1
        end
        (↑Error.assert) -- todo maybe make this "error" with a specific msg
        call ↑Label.abort.toWasmIdent
        unreachable
      end
      i32.const 0
      local.set ↑res
      block ↑fail
        block
          i32.const 1
          local.set ↑sign
          block                 -- first check for a negative sign
            local.get ↑str
            i32.load8_u
            i32.const ↑(Unsigned.ofNat '-'.toNat)
            i32.ne
            br_if 0
            i32.const ↑(-1) -- todo fix
            local.set ↑sign
            local.get ↑str
            i32.const 1
            i32.add
            local.set ↑str      -- increment string if there is a '-'
          end
          loop ↑next
            local.get ↑str
            i32.load8_u
            local.tee ↑c
            i32.eqz
            br_if 1             -- if \0 then end of string
            local.get ↑c
            call ↑is_space_id
            br_if 1             -- encounted a whitespace char
            local.get ↑str
            i32.const 1
            i32.add
            local.set ↑str      -- increment str pointer
            local.get ↑res
            local.get ↑base
            i32.mul
            local.set ↑res      -- shift the number
            local.get ↑c
            i32.const ↑(Unsigned.ofNat '0'.toNat)
            i32.lt_u
            br_if ↑fail
            block
              local.get ↑c
              i32.const ↑(Unsigned.ofNat '9'.toNat)
              i32.gt_u
              br_if 0
              local.get ↑c      -- 0 ≤ c ≤ 9
              i32.const ↑(Unsigned.ofNat '0'.toNat)
              i32.sub
              local.tee ↑c
              local.get ↑base
              i32.ge_u
              br_if ↑fail       -- fail if c ≥ base
              local.get ↑res
              local.get ↑c
              i32.add
              local.set ↑res
              br ↑next          -- successfully parsed digit
            end
            local.get ↑c        -- not a digit between 0-9 (c > '9')
            i32.const ↑(Unsigned.ofNat 'A'.toNat)
            i32.lt_u
            br_if ↑fail         -- fail if c < 'A'
            block
              local.get ↑c
              i32.const ↑(Unsigned.ofNat 'Z'.toNat)
              i32.gt_u
              br_if 0
              local.get ↑c      -- 'A' ≤ c ≤ 'Z'
              i32.const ↑(Unsigned.ofNat 'A'.toNat - 10)
              i32.sub
              local.tee ↑c
              local.get ↑base
              i32.ge_u
              br_if ↑fail       -- fail if c ≥ base
              local.get ↑res
              local.get ↑c
              i32.add
              local.set ↑res
              br ↑next          -- successfully parsed digit
            end
            local.get ↑c        -- not a digit between 0-9 and A-Z
            i32.const ↑(Unsigned.ofNat 'a'.toNat)
            i32.lt_u
            br_if ↑fail         -- fail if c < 'a'
            local.get ↑c
            i32.const ↑(Unsigned.ofNat 'z'.toNat)
            i32.gt_u
            br_if ↑fail         -- fail if c > 'z'
            local.get ↑c        -- 'a' ≤ c ≤ 'z'
            i32.const ↑(Unsigned.ofNat 'a'.toNat - 10)
            i32.sub
            local.tee ↑c
            local.get ↑base
            i32.ge_u
            br_if ↑fail         -- fail if c ≥ base
            local.get ↑res
            local.get ↑c
            i32.add
            local.set ↑res
            br ↑next            -- successfully parsed digit
          end ↑next
        end
        i32.const 1
        local.get ↑res
        local.get ↑sign
        i32.mul                 -- apply sign to res
        local.get ↑str
        return
      end ↑fail
      i32.const 0
      i32.const 0
      local.get ↑str
      return
    ]
  }
where
  str  : Ident := ⟨"str"  , by decide, by decide⟩
  base : Ident := ⟨"base" , by decide, by decide⟩
  c    : Ident := ⟨"c"    , by decide, by decide⟩
  res  : Ident := ⟨"res"  , by decide, by decide⟩
  sign : Ident := ⟨"sign" , by decide, by decide⟩
  next : Ident := ⟨"next" , by decide, by decide⟩
  fail : Ident := ⟨"fail" , by decide, by decide⟩

/- parse_bool : string → bool*
   returns pointer to bool if could parse, otherwise NULL
 -/
def parse_bool : Module.Field := .funcs
  { lbl     := .some parse_bool_id
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := [wat_instr_list|
      block
        block
          local.get 0
          i32.load8_u
          i32.const ↑(Unsigned.ofNat 't'.toNat)
          i32.ne
          br_if 0       -- try parsing false
          local.get 0
          i32.load8_u offset=1
          i32.const ↑(Unsigned.ofNat 'r'.toNat)
          i32.ne
          br_if 1
          local.get 0
          i32.load8_u offset=2
          i32.const ↑(Unsigned.ofNat 'u'.toNat)
          i32.ne
          br_if 1
          local.get 0
          i32.load8_u offset=3
          i32.const ↑(Unsigned.ofNat 'e'.toNat)
          i32.ne
          br_if 1
          local.get 0
          i32.load8_u offset=4
          i32.const 0
          i32.ne
          br_if 1
          i32.const 1
          call ↑Label.calloc.toWasmIdent
          local.tee 0
          i32.const 1
          i32.store8
          local.get 0
          return
        end
        local.get 0
        i32.load8_u
        i32.const ↑(Unsigned.ofNat 'f'.toNat)
        i32.ne
        br_if 0       -- not a bool
        local.get 0
        i32.load8_u offset=1
        i32.const ↑(Unsigned.ofNat 'a'.toNat)
        i32.ne
        br_if 0
        local.get 0
        i32.load8_u offset=2
        i32.const ↑(Unsigned.ofNat 'l'.toNat)
        i32.ne
        br_if 0
        local.get 0
        i32.load8_u offset=3
        i32.const ↑(Unsigned.ofNat 's'.toNat)
        i32.ne
        br_if 0
        local.get 0
        i32.load8_u offset=4
        i32.const ↑(Unsigned.ofNat 'e'.toNat)
        i32.ne
        br_if 0
        local.get 0
        i32.load8_u offset=5
        i32.const 0
        i32.ne
        br_if 0
        i32.const 1
        call ↑Label.calloc.toWasmIdent
        local.tee 0
        i32.const 0
        i32.store8
        local.get 0
        return
      end
      i32.const 0
      return
    ]
  }

/- parse_int : string × (base : int) → bool*
   base must be between 2 and 36 returns pointer to int if could parse,
   otherwise NULL
 -/
def parse_int : Module.Field := .funcs
  { lbl     := .some parse_int_id
  , typeuse := .elab_param_res [(str, .num .i32), (base, .num .i32)] [.num .i32]
  , locals  := [⟨succ, .num .i32⟩]
  , body    := [wat_instr_list|
      local.get ↑str
      local.get ↑base
      call ↑take_int_id
      local.set ↑str
      local.set ↑base   -- int
      local.set ↑succ
      block
        local.get ↑str
        i32.load8_u
        i32.eqz
        br_if 0
        i32.const 0     -- ended on non-null char
        return
      end
      block
        local.get ↑succ
        br_if 0
        i32.const 0     -- didn't parse
        return
      end
      i32.const 4
      call ↑Label.calloc.toWasmIdent
      local.tee ↑succ
      local.get ↑base
      i32.store
      local.get ↑succ
      return
    ]
  }
where
  str  : Ident := ⟨"str"  , by decide, by decide⟩
  base : Ident := ⟨"base" , by decide, by decide⟩
  succ : Ident := ⟨"succ" , by decide, by decide⟩

/- num_tokens : string → int -/
def num_tokens : Module.Field := .funcs
  { lbl     := .some num_tokens_id
  , typeuse := .elab_param_res [(str, .num .i32)] [.num .i32]
  , locals  := [⟨res, .num .i32⟩]
  , body    := [wat_instr_list|
      i32.const 0
      local.set ↑res
      block ↑done
        loop ↑cont
          local.get ↑str
          call ↑consume_space_id
          local.tee ↑str
          i32.load8_u
          i32.eqz
          br_if ↑done         -- at \0, end of string
          local.get ↑res      -- increment total number seen
          i32.const 1
          i32.add
          local.set ↑res
          loop                -- try and consume non-spaces
            local.get ↑str
            i32.load8_u
            i32.eqz
            br_if ↑done       -- read a \0, end of string
            local.get ↑str
            i32.load8_u
            call ↑is_space_id
            br_if ↑cont       -- read a space, start over
            local.get ↑str
            i32.const 1
            i32.add
            local.set ↑str    -- increment string
            br 0              -- repeat
          end
        end ↑cont
      end ↑done
      local.get ↑res
      return
    ]
  }
where
  str  : Ident := ⟨"str" , by decide, by decide⟩
  res  : Ident := ⟨"res" , by decide, by decide⟩
  done : Ident := ⟨"done", by decide, by decide⟩
  cont : Ident := ⟨"cont", by decide, by decide⟩

/- int_tokens : string × (base : int) → bool
   Returns true if the string is whitespace separated ints
 -/
def int_tokens : Module.Field := .funcs
  { lbl     := .some int_tokens_id
  , typeuse := .elab_param_res [(str, .num .i32), (base, .num .i32)] [.num .i32]
  , locals  := []
  , body    := [wat_instr_list|
      block ↑fail
        block ↑succ
          local.get ↑str
          call ↑consume_space_id
          local.set ↑str
          loop
            local.get ↑str
            local.get ↑base
            call ↑take_int_id
            local.set ↑str
            drop                -- dont care about the parsed int
            i32.eqz
            br_if ↑fail         -- couldn't parse an int
            local.get ↑str
            call ↑consume_space_id
            local.tee ↑str
            i32.load8_u
            i32.eqz
            br_if ↑succ         -- end of string
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
  str  : Ident := ⟨"str" , by decide, by decide⟩
  base : Ident := ⟨"base", by decide, by decide⟩
  succ : Ident := ⟨"succ", by decide, by decide⟩
  fail : Ident := ⟨"fail", by decide, by decide⟩

/- parse_tokens : string → string[] -/
def parse_tokens : Module.Field := .funcs
  { lbl     := .some parse_tokens_id
  , typeuse := .elab_param_res [(str, .num .i32)] [.num .i32]
  , locals  := [ ⟨toks, .num .i32⟩, ⟨tok, .num .i32⟩, ⟨start, .num .i32⟩
               , ⟨temp, .num .i32⟩, ⟨toksw, .num .i32⟩]
  , body    := [wat_instr_list|
      local.get ↑str
      call ↑num_tokens_id
      local.tee ↑temp
      i32.const 1       -- space for length
      i32.add
      i32.const 8       -- we allocate 8 bites for pointers even if they are 4
      i32.mul
      call ↑Label.calloc.toWasmIdent
      local.tee ↑toks
      local.get ↑temp
      i32.store
      local.get ↑toks
      i32.const 8
      i32.add
      local.tee ↑toks
      local.set ↑toksw
      block ↑done
        loop
          local.get ↑str
          call ↑consume_space_id
          local.tee ↑str
          i32.load8_u
          i32.eqz
          br_if ↑done         -- reached \0 end of string
          local.get ↑str
          local.set ↑start
          block
            loop                -- parse token
              local.get ↑str
              i32.const 1
              i32.add
              local.tee ↑str
              i32.load8_u
              local.tee ↑temp
              i32.eqz
              br_if 1           -- reached \0, save last token
              local.get ↑temp
              call ↑is_space_id
              br_if 1           -- reached space (i.e. end of token)
              br 0
            end
          end                   -- allocate token
          local.get ↑str
          local.get ↑start
          i32.sub               -- length of the parsed token
          local.tee ↑temp
          i32.const 1
          i32.add               -- add space for \0
          call ↑Label.calloc.toWasmIdent
          local.tee ↑tok
          local.get ↑start
          local.get ↑temp
          memory.copy           -- copy token into tok
          local.get ↑toksw
          local.get ↑tok
          i32.store             -- store address in string
          local.get ↑toksw
          i32.const 8
          i32.add
          local.set ↑toksw      -- increment token array
          br 0                  -- repeat
        end
      end ↑done
      local.get ↑toks
      return
    ]
  }
where
  str   : Ident := ⟨"str"  , by decide, by decide⟩
  toks  : Ident := ⟨"toks" , by decide, by decide⟩
  tok   : Ident := ⟨"tok"  , by decide, by decide⟩
  start : Ident := ⟨"start", by decide, by decide⟩
  temp  : Ident := ⟨"temp" , by decide, by decide⟩
  toksw : Ident := ⟨"toksw", by decide, by decide⟩
  done  : Ident := ⟨"done" , by decide, by decide⟩

/- parse_ints : string → int[] -/
def parse_ints : Module.Field := .funcs
  { lbl     := .some parse_ints_id
  , typeuse := .elab_param_res [(str, .num .i32), (base, .num .i32)] [.num .i32]
  , locals  := [⟨arr, .num .i32⟩, ⟨temp, .num .i32⟩, ⟨temp2, .num .i32⟩]
  , body    := [wat_instr_list|
      local.get ↑str
      call ↑num_tokens_id
      local.tee ↑temp
      i32.const 2               -- add additional space for length (8 bytes)
      i32.add
      i32.const 4
      i32.mul
      call ↑Label.calloc.toWasmIdent
      local.tee ↑arr
      local.get ↑temp
      i32.store                 -- store length
      local.get ↑arr
      i32.const 8
      i32.add
      local.tee ↑arr
      local.set ↑temp
      block ↑fail
        block ↑succ
          local.get ↑str
          call ↑consume_space_id
          local.set ↑str
          loop
            local.get ↑str
            local.get ↑base
            call ↑take_int_id
            local.set ↑str
            local.set ↑temp2    -- store parsed int
            i32.eqz
            br_if ↑fail         -- couldn't parse an int
            local.get ↑temp     -- write the int into the array
            local.get ↑temp2
            i32.store
            local.get ↑temp
            i32.const 4
            i32.add             -- increment array writer temp
            local.set ↑temp
            local.get ↑str
            call ↑consume_space_id
            local.tee ↑str
            i32.load8_u
            i32.eqz
            br_if ↑succ
            br 0
          end
        end ↑succ
        local.get ↑arr
        return
      end ↑fail
      ↑Error.assert
      call ↑Label.abort.toWasmIdent
      unreachable
    ]
  }
where
  str   : Ident := ⟨"str"  , by decide, by decide⟩
  base  : Ident := ⟨"base" , by decide, by decide⟩
  temp  : Ident := ⟨"temp" , by decide, by decide⟩
  temp2 : Ident := ⟨"temp2", by decide, by decide⟩
  arr   : Ident := ⟨"arr"  , by decide, by decide⟩
  succ  : Ident := ⟨"succ" , by decide, by decide⟩
  fail  : Ident := ⟨"fail" , by decide, by decide⟩

def imports : List Module.Field := []
def «extern» : List Module.Field :=
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
def lib : List Module.Field := imports ++ intern ++ «extern»

end Parse

def Parse : Library :=
  { imports := Parse.imports
  , extern  := Parse.extern
  , intern  := Parse.intern
  , lib     := Parse.lib
  }
