import C0deine.Utils.Label
import C0deine.Utils.Comparison

-- TODO: implement more!
namespace C0deine.Target.Wasm

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

end Memarg

inductive Instr.Local
| get (i : Int)
| set (i : Int)
| tee (i : Int)

inductive Instr.Global
| get (i : Int)
| set (i : Int)

inductive Instr.Integer (size : Nat)
| const (c : Int)
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
| load (memarg : Memarg size)
| store (memarg : Memarg size)

inductive Branch
| label (lbl : Label)
| num (n : Nat)

inductive Instr
| unreachable
| nop
| block (lbl : Label) (body : List Instr)
| loop (lbl : Label) (body : List Instr)
| br (branch : Branch)
| br_if (branch : Label)
| wasm_return
| call (lbl : Label)
| drop
| select
| i32 (i : Instr.Integer 32)
| i64 (i : Instr.Integer 64)
