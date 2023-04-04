/-
  Outputted WebAssembly (WASM). Importantly WASM is based on a
  stack machine (not a register machine).

  Currently only outputs the WAT format, which is a human readable
  format based on sexp. To generate WASM bytecode, there is a
  wat2wasm utility which will do so.
-/
import C0deine.Context.Label
import C0deine.Utils.Comparison

-- TODO: implement more!
namespace C0deine.Target.Wasm

-- todo: potentially remove memargs?
structure Memarg (n : Nat) where
  align : Option Int
  offset : Option Int

namespace Memarg

def getOffset (memarg : Memarg n) : Int :=
  match memarg.offset with
  | none   => 0
  | some o => o

def getAlign (memarg : Memarg n) : Int :=
  match memarg.align with
  | none   => n
  | some a => a

def toString (memarg : Memarg n) : String :=
  s!"[{memarg.getAlign}, {memarg.getOffset}]"
instance : ToString (Memarg n) where toString := toString

end Memarg

inductive Instr.Local
| get (i : Int)
| set (i : Int)
| tee (i : Int)

def Instr.Local.toString : Instr.Local → String
  | get i => s!"local.get {i}"
  | set i => s!"local.set {i}"
  | tee i => s!"local.tee {i}"
instance : ToString Instr.Local where toString := Instr.Local.toString

inductive Instr.Global
| get (i : Int)
| set (i : Int)

def Instr.Global.toString : Instr.Global → String
  | get i => s!"global.get {i}"
  | set i => s!"global.set {i}"
instance : ToString Instr.Global where toString := Instr.Global.toString

inductive Instr.Integer (size : Nat)
| const (c : Int) -- todo: maybe enforce size
| eqz
| eq
| ne
| lt_s
| lt_u
| gt_s
| gt_u
| add
| sub
| mul
| div_s
| div_u
| rem_s
| rem_u
| and
| or
| xor
| shl
| shr_s
| shr_u
| load
| store

def Instr.Integer.toString : Instr.Integer size → String
  | const c => s!"i{size}.const {c}"
  | eqz => s!"i{size}.eqz"
  | eq => s!"i{size}.eq"
  | ne => s!"i{size}.ne"
  | lt_s => s!"i{size}.lt_s"
  | lt_u => s!"i{size}.lt_u"
  | gt_s => s!"i{size}.gt_s"
  | gt_u => s!"i{size}.gt_u"
  | add => s!"i{size}.add"
  | sub => s!"i{size}.sub"
  | mul => s!"i{size}.mul"
  | div_s => s!"i{size}.div_s"
  | div_u => s!"i{size}.div_u"
  | rem_s => s!"i{size}.rem_s"
  | rem_u => s!"i{size}.rem_u"
  | and => s!"i{size}.and"
  | or => s!"i{size}.or"
  | xor => s!"i{size}.xor"
  | shl => s!"i{size}.shl"
  | shr_s => s!"i{size}.shr_s"
  | shr_u => s!"i{size}.shr_u"
  | load => s!"i{size}.load"
  | store =>s!"i{size}.store"

instance : ToString (Instr.Integer size) where toString := Instr.Integer.toString

inductive Instr.Branch
| label (lbl : Label)
| num (n : Nat)

def Instr.Branch.toString : Branch → String
  | label lbl => s!"{lbl}"
  | num n => s!"{n}"
instance : ToString Instr.Branch where toString := Instr.Branch.toString

inductive Instr
| comment (str : String)
| unreachable
| nop
| block (lbl : Label) (body : List Instr)
| loop (lbl : Label) (body : List Instr)
| br (branch : Instr.Branch)
| br_if (branch : Instr.Branch)
| «return»
| call (lbl : Label)
| drop
| select
| wasm_local (l : Instr.Local)
| wasm_global (g : Instr.Global)
| i32 (i : Instr.Integer 32)
| i64 (i : Instr.Integer 64)

-- Outputs the WAT format for WASM, can be compiled to WASM (for now)
mutual
def Instr.toListStrings (ins : Instr) : List String :=
  match ins with
  | comment str => [s!";; {str}"]
  | unreachable => [s!"unreachable"]
  | nop => [s!"nop"]
  | block lbl body =>
    let body_strs := Instr.listToListStrings body
      |>.map (fun str => s!"\t{str}")
    s!"(block ${lbl}" :: body_strs |>.concat ")"
  | loop lbl body =>
    let body_strs := Instr.listToListStrings body
      |>.map (fun str => s!"\t{str}")
    s!"(loop ${lbl}" :: body_strs |>.concat ")"
  | br branch => [s!"br {branch}"]
  | br_if branch => [s!"br_if {branch}"]
  | «return» => [s!"return"]
  | call lbl => [s!"call ${lbl}"]
  | drop => [s!"drop"]
  | select => [s!"select"]
  | wasm_local l => [l.toString]
  | wasm_global g => [g.toString]
  | i32 i => [i.toString]
  | i64 i => [i.toString]

def Instr.listToListStrings (ins : List Instr) : List String :=
  match ins with
  | [] => []
  | i :: ilst => (Instr.toListStrings i).append (Instr.listToListStrings ilst)
end

termination_by
  Instr.toListStrings i => sizeOf i
  Instr.listToListStrings ilst => sizeOf ilst
