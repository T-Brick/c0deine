/-
  Outputted WebAssembly (WASM). Importantly WASM is based on a
  stack machine (not a register machine).

  Currently only outputs the WAT format, which is a human readable
  format based on sexp. To generate WASM bytecode, there is a
  wat2wasm utility which will do so.
-/
import C0deine.Context.Label
import C0deine.Context.Temp
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

inductive Instr.Accessor
| num (i : UInt64)
| temp (t : Temp)

instance : ToString Instr.Accessor where toString
  | .num i  => toString i
  | .temp t => s!"$t{t.toNat}"

inductive Instr.Local
| get (i : Instr.Accessor)
| set (i : Instr.Accessor)
| tee (i : Instr.Accessor)

instance : ToString Instr.Local where toString
  | .get i => s!"local.get {i}"
  | .set i => s!"local.set {i}"
  | .tee i => s!"local.tee {i}"

inductive Instr.Global
| get (i : Accessor)
| set (i : Accessor)

instance : ToString Instr.Global where toString
  | .get i => s!"global.get {i}"
  | .set i => s!"global.set {i}"

-- todo maybe remove signed/unsigned ops
inductive Instr.Integer (size : Nat)
| const (c : Int) -- todo: maybe enforce size
| eqz
| eq
| ne
| lt (signed : Bool)
| gt (signed : Bool)
| le (signed : Bool)
| ge (signed : Bool)
| add
| sub
| mul
| div (signed : Bool)
| rem (signed : Bool)
| and
| or
| xor
| shl
| shr (signed : Bool)
| load
| load8 (signed : Bool)
| load16 (signed : Bool)
| load32 (signed : Bool)
| store
| store8
| store16
| store32


instance : ToString (Instr.Integer size) where toString
  | .const c      => s!"i{size}.const {c}"
  | .eqz          => s!"i{size}.eqz"
  | .eq           => s!"i{size}.eq"
  | .ne           => s!"i{size}.ne"
  | .lt true      => s!"i{size}.lt_s"
  | .lt false     => s!"i{size}.lt_u"
  | .le true      => s!"i{size}.le_s"
  | .le false     => s!"i{size}.le_u"
  | .gt true      => s!"i{size}.gt_s"
  | .gt false     => s!"i{size}.gt_u"
  | .ge true      => s!"i{size}.ge_s"
  | .ge false     => s!"i{size}.ge_u"
  | .add          => s!"i{size}.add"
  | .sub          => s!"i{size}.sub"
  | .mul          => s!"i{size}.mul"
  | .div true     => s!"i{size}.div_s"
  | .div false    => s!"i{size}.div_u"
  | .rem true     => s!"i{size}.rem_s"
  | .rem false    => s!"i{size}.rem_u"
  | .and          => s!"i{size}.and"
  | .or           => s!"i{size}.or"
  | .xor          => s!"i{size}.xor"
  | .shl          => s!"i{size}.shl"
  | .shr true     => s!"i{size}.shr_s"
  | .shr false    => s!"i{size}.shr_u"
  | .load         => s!"i{size}.load"
  | .load8 false  => s!"i{size}.load8_u"
  | .load16 false => s!"i{size}.load16_u"
  | .load32 false => s!"i{size}.load32_u"
  | .load8  true  => s!"i{size}.load8_s"
  | .load16 true  => s!"i{size}.load16_s"
  | .load32 true  => s!"i{size}.load32_s"
  | .store        => s!"i{size}.store"
  | .store8       => s!"i{size}.store8"
  | .store16      => s!"i{size}.store16"
  | .store32      => s!"i{size}.store32"

inductive Instr.Branch
| label (lbl : Label)
| num (n : Nat)

def Instr.Branch.toString : Branch → String
  | label lbl => s!"${lbl}"
  | num n => s!"{n}"
instance : ToString Instr.Branch where toString := Instr.Branch.toString

inductive Instr
| comment (str : String)
| unreachable
| nop
| block (lbl : Option Label) (body : List Instr)
| loop (lbl : Option Label) (body : List Instr)
| br (branch : Instr.Branch)
| br_if (branch : Instr.Branch)
| «return»
| call (lbl : Label)
| drop
| select
| mem_size
| mem_grow
| wasm_local (l : Instr.Local)
| wasm_global (g : Instr.Global)
| i32 (i : Instr.Integer 32)
| i32_wrap_i64
| i64 (i : Instr.Integer 64)
| i64_extend_i32_u

-- this is temporary until WASM library is working enough to transition
-- todo add result
structure Func where
  name : Label
  args : List SizedTemp
  locals : List Temp -- todo make sized
  body : List Instr

def Prog := List Func

-- Outputs the WAT format for WASM, can be compiled to WASM (for now)
mutual
def Instr.toListStrings (ins : Instr) : List String :=
  match ins with
  | comment str => [s!";; {str}"]
  | unreachable => [s!"unreachable"]
  | nop => [s!"nop"]
  | block lOpt body =>
    let body_strs := Instr.listToListStrings body
      |>.map (fun str => s!"  {str}")
    let header :=
      match lOpt with
      | none => "(block"
      | some lbl => s!"(block ${lbl} (param i32)" -- this is not correct but allows testing
    header :: body_strs |>.concat ")"
  | loop lOpt body =>
    let body_strs := Instr.listToListStrings body
      |>.map (fun str => s!"  {str}")
    let header :=
      match lOpt with
      | none => "(loop"
      | some lbl => s!"(loop ${lbl}"
    header :: body_strs |>.concat ")"
  | br branch => [s!"br {branch}"]
  | br_if branch => [s!"br_if {branch}"]
  | «return» => [s!"return"]
  | call lbl => [s!"call ${lbl}"]
  | drop => ["drop"]
  | select => ["select"]
  | mem_size => ["memory.size"]
  | mem_grow => ["memory.grow"]
  | wasm_local l => [toString l]
  | wasm_global g => [toString g]
  | i32 i => [toString i]
  | i32_wrap_i64 => ["i32.wrap_i64"]
  | i64 i => [toString i]
  | i64_extend_i32_u => ["i64.extend_i32_u"]

def Instr.listToListStrings (ins : List Instr) : List String :=
  match ins with
  | [] => []
  | i :: ilst => (Instr.toListStrings i).append (Instr.listToListStrings ilst)
end
termination_by
  Instr.toListStrings i => sizeOf i
  Instr.listToListStrings ilst => sizeOf ilst

instance : ToString Instr where
  toString := String.intercalate "\n" ∘ Instr.toListStrings
instance : ToString (List Instr) where
  toString := String.intercalate "\n" ∘ List.map toString

def arg_toString (st : SizedTemp) :=
  match st.size with
  | .byte -- todo fix
  | .word
  | .double => s!"$t{st.data.toNat} i32"
  | .quad   => s!"$t{st.data.toNat} i64"

nonrec def Func.toString (f : Func) : String :=
  let args :=
    f.args.map (fun st => s!"(param {arg_toString st})")
    |> String.intercalate " "
  let temps :=
    f.locals.map (fun t => s!"(local $t{t.toNat} i32)") -- todo size
    |> String.intercalate "\n  "
  let body := (String.intercalate "\n  " ∘ List.map toString) f.body
  s!"(func ${f.name} {args} (result i32)\n  {temps}\n  {body}\n)"
instance : ToString Func := ⟨Func.toString⟩

nonrec def Prog.toString (prog : Prog) : String :=
  let funcs := prog.map toString |> String.intercalate "\n\n"
  let log := "(import \"console\" \"log\" (func $log (param i32)))"
  let abort := "(func $abort (i32.const -1) (call $log) unreachable)"
  let header := s!"(module {log} {abort}"
  let invoke := "(func $main (call $_c0_main) (call $log))\n\n(start $main)"
  s!"{header}\n\n{funcs}\n\n{invoke})"
instance : ToString Prog := ⟨Prog.toString⟩
