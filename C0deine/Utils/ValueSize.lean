import Wasm.Syntax.Typ

namespace C0deine

inductive ValueSize
| byte
| word
| double
| quad

namespace ValueSize

def bytes : ValueSize → Nat
  | .byte   => 1
  | .word   => 2
  | .double => 4
  | .quad   => 8

def bits : ValueSize → Nat
  | .byte   => 8
  | .word   => 16
  | .double => 32
  | .quad   => 64

def wasm_val_type : ValueSize → Wasm.Syntax.Typ.Val
  | .byte   => .num .i32
  | .word   => .num .i32
  | .double => .num .i32
  | .quad   => .num .i64

def toString : ValueSize → String
  | byte   => "b"
  | word   => "w"
  | double => "l"
  | quad   => "q"
instance : ToString ValueSize where toString := ValueSize.toString

end ValueSize

structure Sized (α : Type) where
  size : ValueSize
  data : α
