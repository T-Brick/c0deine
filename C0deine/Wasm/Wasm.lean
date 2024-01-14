/- C0deine - Wasm
   Some utilities for creating WASM instructions more easily. Also contains the
   necessary module fields for generating a complete module when given the
   compile C0 code.
   - Thea Brick
 -/
import Numbers
import C0deine.Context.Label
import C0deine.Context.Temp
import C0deine.Config.Targets
import Wasm.Notation
import Wasm.Text.Module
import Wasm.Binary.Module

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
  .block (.block l (.value .none) ins .wasm_end .none)
def loop (l : Wasm.Text.Label) (ins : List Instr) : Instr :=
  .block (.loop l (.value .none) ins .wasm_end .none)

def temp  : Temp      → Module.Index := .name ∘ Temp.toWasmIdent
-- def stemp : SizedTemp → Module.Index := .name ∘ SizedTemp.toWasmIdent
def stemp : SizedTemp → Module.Index :=
  .name ∘ Temp.toWasmIdent ∘ SizedTemp.temp
def label : Label     → Module.Index := .name ∘ Label.toWasmIdent

def br : Module.Index.Label → Instr      := .plain ∘ .br
def br_if : Module.Index.Label → Instr   := .plain ∘ .br_if
def call : Module.Index.Function → Instr := .plain ∘ .call
def wasm_return : Instr                  := .plain .wasm_return
def unreachable : Instr                  := .plain .unreachable

/- We pass the signal numbers we want into the abort function
    (nb. div-by-zero is already a wasm exception)
-/
def Error.mem    : Instr := i32_const 12    -- SIGUSR2
def Error.assert : Instr := i32_const 6     -- SIGABRT
def Error.arith  : Instr := i32_const 8     -- SIGFPE


/- Module Field implementations/utils for a compiled C0 program. -/
open Wasm.Text.Notation

def c0deine : Name :=
  ⟨"c0deine", by simp [String.length, Wasm.Vec.max_length]; linarith⟩

def result_id : Ident := ⟨"result", sorry, sorry⟩
def result_import : Module.Field := .imports
  ⟨ c0deine
  , ⟨"result" , by simp [String.length, Wasm.Vec.max_length]; linarith⟩
  , .func (.some result_id) (.elab_param_res [(.none, .num .i32)] [])
  ⟩

def calloc_func : Module.Field := .funcs
  { lbl     := .some Label.calloc.toWasmIdent
  , typeuse := .elab_param_res [(.none, .num .i32)] [.num .i32]
  , locals  := [⟨.none, .num .i32⟩]
  , body    := [wat_instr_list|
      local.get 0           -- get arg (ie. sizeOf type)
      i32.const 0           -- get next free pointer after alloc
      i32.load
      i32.add
      local.set 1
      block
        loop                -- loop to increase memory size
          local.get 1
          memory.size       -- returns number of pages
          i32.const 65536   -- pagesize
          i32.mul
          i32.lt_u
          br_if 1           -- next ptr within bounds, don't grow
          i32.const 1       -- grow by 1 page
          memory.grow
          br 0
        end
      end
      i32.const 0           -- need to zero out the memory
      i32.load
      i32.const 0
      local.get 0
      memory.fill
      i32.const 0           -- address we want to return
      i32.load
      i32.const 0
      local.get 1
      i32.store             -- update free pointer
      return
    ]
  }
def calloc_import : Module.Field := .imports
  ⟨ c0deine
  , ⟨"calloc" , by simp [String.length, Wasm.Vec.max_length]; linarith⟩
  , .func (.some Label.calloc.toWasmIdent)
          (.elab_param_res [(.none, .num .i32)] [])
  ⟩

def free_func : Module.Field := .funcs
  { lbl     := .some Label.free.toWasmIdent
  , typeuse := .elab_param_res [(.none, .num .i32)] []
  , locals  := []
  , body    :=
    [ .comment "TODO: implement free"
    , Plain.wasm_return
    ]
  }
def free_import : Module.Field := .imports
  ⟨ c0deine
  , ⟨"free" , by simp [String.length, Wasm.Vec.max_length]; linarith⟩
  , .func (.some Label.free.toWasmIdent)
          (.elab_param_res [(.none, .num .i32)] [])
  ⟩

def abort_func : Module.Field := .funcs
  { lbl     := .some Label.abort.toWasmIdent
  , typeuse := .elab_param_res [(.none, .num .i32)] []
  , locals  := []
  , body    := [wat_instr_list|
      local.get 0
      call ↑result_id
      unreachable
    ]
  }
def abort_import : Module.Field := .imports
  ⟨ c0deine
  , ⟨"abort"  , by simp [String.length, Wasm.Vec.max_length]; linarith⟩
  , .func (.some Label.abort.toWasmIdent)
          (.elab_param_res [(.none, .num .i32)] [])
  ⟩

def error_import : Module.Field := .imports
  ⟨ c0deine
  , ⟨"error"  , by simp [String.length, Wasm.Vec.max_length]; linarith⟩
  , .func (.some Label.error.toWasmIdent)
          (.elab_param_res [(.none, .num .i32)] [])
  ⟩

def debug_import : Module.Field := .imports
  ⟨ c0deine
  , ⟨"debug"  , by simp [String.length, Wasm.Vec.max_length]; linarith⟩
  , .func (.some Label.debug.toWasmIdent)
          (.elab_param_res [(.none, .num .i32)] [.num .i32])
  ⟩

def memory_import : Module.Field := .imports
  ⟨ c0deine
  , ⟨"memory" , by simp [String.length, Wasm.Vec.max_length]; linarith⟩
  , .mem .none ⟨1, .none⟩
  ⟩

def start  : Module.Field := .start ⟨.name Label.main.toWasmIdent⟩

def main_import : Module.Field := .imports
  ⟨ ⟨"c0deine", by simp [String.length, Wasm.Vec.max_length]; linarith⟩
  , ⟨"main"   , by simp [String.length, Wasm.Vec.max_length]; linarith⟩
  , .func (.some Label.main.toWasmIdent) (.elab_param_res [] [])
  ⟩

def main (config : Wasm.Config) : List Module.Field :=
  let main_body := [Plain.call (.name ⟨"_c0_main", sorry, sorry⟩)]
  match config.main with
  | .import =>
    [ .exports
        ⟨ ⟨"_c0_main", by simp [String.length, Wasm.Vec.max_length]; linarith⟩
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
