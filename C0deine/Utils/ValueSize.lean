
namespace C0deine

inductive ValueSize
| byte
| word
| double
| quad

namespace ValueSize

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
