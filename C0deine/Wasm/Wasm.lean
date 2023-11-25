import Numbers
import C0deine.Context.Label
import C0deine.Context.Temp
import C0deine.Config.Targets
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

/- We pass the signal numbers we want into the abort function
    (nb. div-by-zero is already a wasm exception)
-/
def Error.mem    : Instr := i32_const 12    -- SIGUSR2
def Error.assert : Instr := i32_const 6     -- SIGABRT
def Error.arith  : Instr := i32_const 8     -- SIGFPE

/- todo move into proper std libraries -/
def result_id : Ident := ⟨"result", sorry, sorry⟩
def result : Module.Field := .imports
  ⟨ "c0deine"
  , "result"
  , .func (.some result_id) (.elab_param_res [(.none, .num .i32)] [])
  ⟩

def calloc_func : Module.Field := .funcs
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
def calloc_import : Module.Field := .imports
  ⟨ "c0deine"
  , "calloc"
  , .func (.some Label.calloc.toWasmIdent)
          (.elab_param_res [(.none, .num .i32)] [])
  ⟩

def abort_func : Module.Field := .funcs
  { lbl     := .some Label.abort.toWasmIdent
  , typeuse := .elab_param_res [(.none, .num .i32)] []
  , locals  := []
  , body    :=
    [ locl (.get (.num 0))
    , Plain.call (.name result_id)
    , Plain.unreachable
    ]
  }
def abort_import : Module.Field := .imports
  ⟨ "c0deine"
  , "abort"
  , .func (.some Label.abort.toWasmIdent)
          (.elab_param_res [(.none, .num .i32)] [])
  ⟩

def start  : Module.Field := .start ⟨.name Label.main.toWasmIdent⟩

def main_import : Module.Field := .imports
  ⟨ "c0deine"
  , "main"
  , .func (.some Label.main.toWasmIdent) (.elab_param_res [] [])
  ⟩

def main (config : Wasm.Config) : List Module.Field :=
  let main_body := (
    if config.import_calloc then [] else
      [ (i32_const 0)               -- store pointer to next free seg at 0
      , (i32_const 4)
      , (i32_mem (.store ⟨0, 4⟩))
      ]
    ).append [Plain.call (.name ⟨"_c0_main", sorry, sorry⟩)]
  match config.main with
  | .import =>
    [ .exports
        ⟨ "_c0_main"
        , .func (.name ⟨"_c0_main", sorry, sorry⟩)
        ⟩
    ]
  | .start  => [start, .funcs
    { lbl     := .some Label.main.toWasmIdent
    , typeuse := .elab_param_res [] []
    , locals  := []
    , body    := main_body.append [Plain.call (.name result_id)]
    }]
  | .return => [.funcs
    { lbl     := .some Label.main.toWasmIdent
    , typeuse := .elab_param_res [] [.num .i32]
    , locals  := []
    , body    := main_body
    }]

def memory : Module.Field := .mems ⟨.none, ⟨1, .none⟩⟩

def mkImports (config : Wasm.Config) : List (Module.Field) :=
  [ .some result
  , if config.import_abort then .some abort_import else .none
  , if config.import_calloc then .some calloc_import else .none
  , match config.main with | .import => .some main_import | _ => .none
  ].filterMap (·)

def mkModule (config : Wasm.Config) (funcs : List Module.Function) : Module :=
  let c0_funcs := funcs.map .funcs
  ⟨ .none
  , mkImports config
    ++ [ .some memory
       , if config.import_abort then .none else .some abort_func
       , if config.import_calloc then .none else .some calloc_func
       ].filterMap (·)
    ++ (main config)
    ++ c0_funcs
  ⟩
