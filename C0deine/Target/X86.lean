/-
Outputted x86-64 assembly that should be executed by a linker

Should be generated from the 2-address abstract assembly
-/

import C0deine.Utils.Register
import C0deine.Utils.Label
import C0deine.Utils.Comparison

namespace C0deine.Target.X86

def validMemoryScale : Nat → Prop
| 1 | 2 | 4 | 8 => true
| _ => false

def Memory.Scale := { n // validMemoryScale n }

structure Memory where
  disp : Int
  base : Register
  index : Option Register
  scale : Memory.Scale

def Memory.displacementToString : Int → String
  | 0 => ""
  | n => s!"{n}"

def Memory.scaleToString (m : Memory.Scale) : String :=
  match m.val with
  | 1 => ""
  | n => s!", {n}"

instance : ToString Memory.Scale where toString := Memory.scaleToString

def Memory.toString (mem : Memory) : String :=
  match mem.index with
  | none => s!"{Memory.displacementToString mem.disp}({mem.base})"
  | some index_reg => s!"{Memory.displacementToString mem.disp}({mem.base}, {index_reg}{mem.scale})"
instance : ToString Memory where toString := Memory.toString

inductive Operand
| const (c : Int)
| reg (r : Register.SizedRegister)
| mem (m : Memory)

def Operand.toString : Operand → String
  | const c => s!"{c}"
  | reg r   => s!"{r}"
  | mem m   => s!"{m}"
instance : ToString Operand where toString := Operand.toString

inductive Instr
| label (lbl : Label)
| directive (str : String)
| comment (str : String)
| mov (src dest : Operand) (size : Register.Size)
| lea (src dest : Operand) (size : Register.Size)
| add (src dest : Operand) (size : Register.Size)
| sub (src dest : Operand) (size : Register.Size)
| imul (src : Operand) (size : Register.Size)
| idiv (src : Operand) (size : Register.Size)
| not (dest : Operand) (size : Register.Size)
| and (src dest : Operand) (size : Register.Size)
| xor (src dest : Operand) (size : Register.Size)
| or (src dest : Operand) (size : Register.Size)
| sal (src dest : Operand) (size : Register.Size)
| sar (src dest : Operand) (size : Register.Size)
| cdq
| cmp (lhs : Operand) (rhs : Operand) (size : Register.Size)
| setcc (cc : Comparator) (dest : Operand)
| jmp (lbl : Label)
| jcc (cc : Comparator) (lbl : Label)
| call (lbl : Label)
| ret
| push (src : Operand)
| pop (dest : Operand)

def Instr.binopToString
    (instr : String)
    (src dest : Operand)
    : String :=
  s!"\t{instr}\t\t{src}, {dest}"

def Instr.toString : Instr → String
  | label (lbl : Label) => s!"{lbl}:"
  | directive (str : String) => s!".{str}"
  | comment (str : String) => s!"#{str}"
  | mov (src : Operand) (dest : Operand) (size : Register.Size) =>
      Instr.binopToString s!"mov{size}" src dest
  | lea (src : Operand) (dest : Operand) (size : Register.Size) =>
      Instr.binopToString s!"lea{size}" src dest
  | add (src : Operand) (dest : Operand) (size : Register.Size) =>
      Instr.binopToString s!"add{size}" src dest
  | sub (src : Operand) (dest : Operand) (size : Register.Size) =>
      Instr.binopToString s!"sub{size}" src dest
  | imul (src : Operand) (size : Register.Size) =>
      s!"\timul{size}\t\t{src}"
  | idiv (src : Operand) (size : Register.Size) =>
      s!"\tidiv{size}\t\t{src}"
  | not (dest : Operand) (size : Register.Size) =>
      s!"\tnot\t\t{dest}"
  | and (src : Operand) (dest : Operand) (size : Register.Size) =>
      Instr.binopToString s!"and" src dest
  | xor (src : Operand) (dest : Operand) (size : Register.Size) =>
      Instr.binopToString s!"xor" src dest
  | or (src : Operand) (dest : Operand) (size : Register.Size) =>
      Instr.binopToString s!"or" src dest
  | sal (src : Operand) (dest : Operand) (size : Register.Size) =>
      Instr.binopToString s!"sal{size}" src dest
  | sar (src : Operand) (dest : Operand) (size : Register.Size) =>
      Instr.binopToString s!"sar{size}" src dest
  | cdq => "\tcdq"
  | cmp (lhs : Operand) (rhs : Operand) (size : Register.Size) =>
      Instr.binopToString s!"cmp{size}" lhs rhs
  | setcc (cc : Comparator) (dest : Operand) =>
      s!"\tset{cc}\t\t{dest}"
  | jmp (lbl : Label) =>
      s!"\tjmp\t\t{lbl}"
  | jcc (cc : Comparator) (lbl : Label) =>
      s!"\tjmp{cc}\t\t{lbl}"
  | call (lbl : Label) =>
      s!"\tcall\t\t{lbl}"
  | ret =>
      s!"\tret"
  | push (src : Operand) =>
      s!"\tpushq\t\t{src}"
  | pop (dest : Operand) =>
      s!"\tpopq\t\t{dest}"

end X86
