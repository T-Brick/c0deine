import Numbers
import C0deine.Context.Label
import C0deine.Context.Temp
import Wasm.Text.Instr
import Wasm.Text.Index
import Wasm.Text.Module

namespace C0deine.Target.Wasm

open Numbers Wasm.Text Wasm.Text.Instr Wasm.Syntax.Instr.Numeric
  Wasm.Syntax.Instr.Memory

def i_eqz (nn : Size) : Wasm.Syntax.Instr.Numeric nn :=
  Wasm.Syntax.Instr.Numeric.integer (Integer.test (nn := nn) .eqz)
def i_const (nn : Size)
    : Numbers.Unsigned nn.toBits → Wasm.Syntax.Instr.Numeric nn :=
  Wasm.Syntax.Instr.Numeric.integer ∘ Integer.const
def i_un (nn : Size) : Integer.Unop → Wasm.Syntax.Instr.Numeric nn :=
  Wasm.Syntax.Instr.Numeric.integer ∘ Integer.unop (nn := nn)
def i_bin (nn : Size) : Integer.Binop → Wasm.Syntax.Instr.Numeric nn :=
  Wasm.Syntax.Instr.Numeric.integer ∘ Integer.binop (nn := nn)
def i_rel (nn : Size) : Integer.Relation → Wasm.Syntax.Instr.Numeric nn :=
  Wasm.Syntax.Instr.Numeric.integer ∘ Integer.relation (nn := nn)

def i32_mem : Wasm.Syntax.Instr.Memory.Integer .double → Instr :=
  Instr.plain ∘ Instr.Plain.memory ∘ Instr.Memory.integer
def i64_mem : Wasm.Syntax.Instr.Memory.Integer .quad → Instr :=
  Instr.plain ∘ Instr.Plain.memory ∘ Instr.Memory.integer

def num_to_instr : Wasm.Syntax.Instr.Numeric nn → Instr :=
  Instr.plain ∘ Instr.Plain.numeric

def i32_eqz   : Instr                    := num_to_instr (i_eqz .double)
def i32_un    : Integer.Unop     → Instr := num_to_instr ∘ i_un .double
def i32_bin   : Integer.Binop    → Instr := num_to_instr ∘ i_bin .double
def i32_rel   : Integer.Relation → Instr := num_to_instr ∘ i_rel .double
def i32_const : Unsigned32       → Instr := num_to_instr ∘ i_const .double

def i64_const : Unsigned64       → Instr := num_to_instr ∘ i_const .quad
def i64_bin   : Integer.Binop    → Instr := num_to_instr ∘ i_bin .quad
def i64_rel   : Integer.Relation → Instr := num_to_instr ∘ i_rel .quad

def locl  : Instr.Local → Instr := .plain ∘ .locl
def globl : Instr.Local → Instr := .plain ∘ .locl
def block (l : Wasm.Text.Label) (ins : List Instr) : Instr :=
  .block (.block l (.value .none) ins .none)
def loop (l : Wasm.Text.Label) (ins : List Instr) : Instr :=
  .block (.loop l (.value .none) ins .none)

def temp  : Temp      → Module.Index := .name ∘ Temp.toWasmIdent
-- def stemp : SizedTemp → Module.Index := .name ∘ SizedTemp.toWasmIdent
def stemp : SizedTemp → Module.Index :=
  .name ∘ Temp.toWasmIdent ∘ SizedTemp.temp
def label : Label     → Module.Index := .name ∘ Label.toWasmIdent

def calloc : Module.Field := .funcs
  { lbl     := .some Label.calloc.toWasmIdent
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.some Temp.general.toWasmIdent, .num .i32⟩]
  , body    :=
    [ locl (.get (.num 0))            -- get arg (ie. sizeOf type)
    , i32_const 0
    , i32_mem (.load ⟨0, 4⟩)          -- 0 address has ptr to next free seg
    , i32_bin .add                    -- get next free pointer after alloc
    , locl (.set (temp Temp.general))
    , block .no_label
      [ loop .no_label                -- loop to increase memory size
        [ locl (.get (temp Temp.general))
        , Plain.memory .size          -- returns number of pages
        , i32_const 65536             -- pagesize
        , i32_bin .mul
        , i32_rel (.lt .u)
        , Plain.br_if (.num 1)        -- next ptr within bounds, don't grow
        , i32_const 1                 -- grow by 1 page
        , Plain.memory .grow
        , Plain.br (.num 0)
        ]
      ]
    , i32_const 0
    , i32_mem (.load ⟨0, 4⟩)          -- pointer we want to return
    , i32_const 0
    , locl (.get (temp Temp.general))
    , i32_mem (.store ⟨0, 4⟩)         -- update free pointer
    , Plain.wasm_return
    ]
  }

def abort : Module.Field := .funcs
  { lbl     := .some Label.abort.toWasmIdent
  , typeuse := .elab_param_res [] []
  , locals  := []
  , body    :=
    [ i32_const (-1)
    , Plain.unreachable
    ]
  }

def log_id : Ident := ⟨"log", sorry, sorry⟩
def log : Module.Field := .imports
  ⟨ "console"
  , "log"
  , .func (.some log_id) (.elab_param_res [(.none, .num .i32)] [])
  ⟩

def main_func : Module.Function := 
  { lbl     := .some Label.main.toWasmIdent
  , typeuse := .elab_param_res [] []
  , locals  := []
  , body    :=
    [ (i32_const 0)               -- store pointer to next free seg at 0
    , (i32_const 4)
    , (i32_mem (.store ⟨0, 4⟩))
    , Plain.call (.name ⟨"_c0_main", sorry, sorry⟩)
    ]
  }

def main : Module.Field := .funcs main_func

def main_log : Module.Field := .funcs
  { main_func with body := main_func.body ++ [.plain <|.call (.name log_id)] }

def memory : Module.Field := .mems ⟨.none, ⟨1, .none⟩⟩
def start  : Module.Field := .start ⟨.name Label.main.toWasmIdent⟩

def mkModule (funcs : List Module.Function) : Module :=
  ⟨.none, [log, abort, memory, calloc, main_log, start] ++ funcs.map .funcs⟩
