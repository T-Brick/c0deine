import C0deine.Utils.Temp
import C0deine.Utils.Register
import C0deine.Utils.Label
import C0deine.Utils.Comparison

namespace C0deine.AbsAsm2

inductive Operand
| const (c : Int)
| mem (m : Int)
| temp (t : Temp)
| reg (r : Register)

structure Addr where
  base : Temp
  offset : Int
  index : Option Temp
  scale : Int

inductive Instr
| label (lbl : Label)
| directive (str : String)
| comment (str : String)
| mov (src dest : Operand)
| add (src dest : Operand)
| sub (src dest : Operand)
| mul (src : Operand)
| divmod (src : Operand)
| and (src dest : Operand)
| xor (src dest : Operand)
| or (src dest : Operand)
| sal (src dest : Operand)
| sar (src dest : Operand)
| cmp (cmp : Comparator) (lhs rhs : Operand)
| jump (lbl : Label)
| cjump (lbl : Label)
| call (lbl : Label)
| ret
| load (src : Addr) (dest : Operand)
| store (src : Operand) (dest : Addr)
| null_check (check : Operand)
| shift_check (check : Operand)
| bounds_check (src : Temp) (index : Operand)
