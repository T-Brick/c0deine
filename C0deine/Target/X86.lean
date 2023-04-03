/-
  Outputted x86-64 assembly that should be executed by a linker.

  Should be generated from the 2-address abstract assembly.
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
| reg (r : SizedRegister)
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
| mov (src dest : Operand) (size : ValueSize)
| lea (src dest : Operand) (size : ValueSize)
| add (src dest : Operand) (size : ValueSize)
| sub (src dest : Operand) (size : ValueSize)
| imul (src : Operand) (size : ValueSize)
| idiv (src : Operand) (size : ValueSize)
| not (dest : Operand) (size : ValueSize)
| and (src dest : Operand) (size : ValueSize)
| xor (src dest : Operand) (size : ValueSize)
| or (src dest : Operand) (size : ValueSize)
| sal (src dest : Operand) (size : ValueSize)
| sar (src dest : Operand) (size : ValueSize)
| cdq
| cmp (lhs : Operand) (rhs : Operand) (size : ValueSize)
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
  | mov (src : Operand) (dest : Operand) size =>
      Instr.binopToString s!"mov{size}" src dest
  | lea (src : Operand) (dest : Operand) size =>
      Instr.binopToString s!"lea{size}" src dest
  | add (src : Operand) (dest : Operand) size =>
      Instr.binopToString s!"add{size}" src dest
  | sub (src : Operand) (dest : Operand) size =>
      Instr.binopToString s!"sub{size}" src dest
  | imul (src : Operand) size =>
      s!"\timul{size}\t\t{src}"
  | idiv (src : Operand) size =>
      s!"\tidiv{size}\t\t{src}"
  | not (dest : Operand) _size =>
      s!"\tnot\t\t{dest}"
  | and (src : Operand) (dest : Operand) _size =>
      Instr.binopToString s!"and" src dest
  | xor (src : Operand) (dest : Operand) _size =>
      Instr.binopToString s!"xor" src dest
  | or (src : Operand) (dest : Operand) _size =>
      Instr.binopToString s!"or" src dest
  | sal (src : Operand) (dest : Operand) size =>
      Instr.binopToString s!"sal{size}" src dest
  | sar (src : Operand) (dest : Operand) size =>
      Instr.binopToString s!"sar{size}" src dest
  | cdq => "\tcdq"
  | cmp (lhs : Operand) (rhs : Operand) size =>
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
