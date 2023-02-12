/-
  An abstract assembly that only supports 2-addresses, this makes
  it quiet similar to x86-64 but without some of the extra details.
-/
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

def Operand.toString : Operand → String
  | const c => s!"${c}"
  | mem m => s!"m{m}"
  | temp t => s!"{t}"
  | reg r => s!"{r}"
instance : ToString Operand where toString := Operand.toString

structure Addr where
  base : Temp
  offset : Int
  index : Option Temp
  scale : Int

instance : ToString Addr where
  toString | addr => s!"{addr.base}, {addr.offset}, {addr.index} {addr.scale}"


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
| cmp (c : Comparator) (lhs rhs : Operand)
| jump (lbl : Label)
| cjump (lbl : Label)
| call (lbl : Label)
| ret
| load (src : Addr) (dest : Operand)
| store (src : Operand) (dest : Addr)
| null_check (check : Operand)
| shift_check (check : Operand)
| bounds_check (src : Temp) (index : Operand)

def Instr.toString : Instr → String
  | label (lbl : Label) => s!"{lbl}:"
  | directive (str : String) => s!".{str}"
  | comment (str : String) => s!"#{str}"
  | mov (src : Operand) (dest : Operand) => s!"\tmov\t\t{src}, {dest}"
  | add (src : Operand) (dest : Operand) => s!"\tadd\t\t{src}, {dest}"
  | sub (src : Operand) (dest : Operand) => s!"\tsub\t\t{src}, {dest}"
  | mul (src : Operand) => s!"\tmul\t\t{src}"
  | divmod (src : Operand) => s!"\tdivmod\t\t{src}"
  | and (src : Operand) (dest : Operand) => s!"\tand\t\t{src}, {dest}"
  | xor (src : Operand) (dest : Operand) => s!"\txor\t\t{src}, {dest}"
  | or (src : Operand) (dest : Operand) => s!"\tor\t\t{src}, {dest}"
  | sal (src : Operand) (dest : Operand) => s!"\tsal\t\t{src}, {dest}"
  | sar (src : Operand) (dest : Operand) => s!"\tsar\t\t{src}, {dest}"
  | cmp (c : Comparator) (lhs : Operand) (rhs : Operand) => s!"\tcmp\t\t{lhs} {c} {rhs}"
  | jump (lbl : Label) => s!"\tjump\t\t{lbl}"
  | cjump (lbl : Label) => s!"\tcjump\t\t{lbl}"
  | call (lbl : Label) => s!"\tcall\t\t{lbl}"
  | ret => s!"\tret"
  | load (src : Addr) (dest : Operand) => s!"\tload\t\t{src}, {dest}"
  | store (src : Operand) (dest : Addr) => s!"\tstore\t\t{src}, {dest}"
  | null_check (check : Operand) => s!"\tnull?\t\t{check}"
  | shift_check (check : Operand) => s!"\tshift?\t\t{check}"
  | bounds_check (src : Temp) (index : Operand) => s!"\tbounds?\t\t{src}[{index}]"
