import C0deine.Utils.Symbol

namespace C0deine

mutual
inductive Typ
| prim (prim : Typ.Primitive)
| mem (mem : Typ.Memory)
| void
| alias (sym : Symbol)

inductive Typ.Primitive
| int
| bool

inductive Typ.Memory
| pointer (typ : Typ)
| array (typ : Typ)
| struct (sym : Symbol)
end

namespace C0deine.Typ

mutual
def Primitive.toString : Typ.Primitive → String
  | .int  => "int"
  | .bool => "bool"
instance : ToString Typ.Primitive where toString := Typ.Primitive.toString

def Memory.toString : Typ.Memory → String
  | .pointer (typ : Typ)   => s!"{Typ.toString typ} *"
  | .array (typ : Typ)     => s!"{Typ.toString typ}[]"
  | .struct (sym : Symbol) => s!"struct {sym}"
instance : ToString Typ.Memory where toString := Typ.Memory.toString

def Typ.toString : Typ → String
  | .prim (prim : Typ.Primitive) => Typ.Primitive.toString prim
  | .mem (mem : Typ.Memory) => Typ.Memory.toString mem
  | .void => "void"
  | .alias (sym : Symbol) => s!"{sym}"
instance : ToString Typ where toString := Typ.toString
end
