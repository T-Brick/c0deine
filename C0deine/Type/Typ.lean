import C0deine.Context.Symbol

namespace C0deine

inductive Typ.Primitive
| int
| bool
deriving DecidableEq, Inhabited, Hashable

mutual
inductive Typ
| any
| prim (p : Typ.Primitive)
| mem (m : Typ.Memory)
deriving Inhabited, Hashable

inductive Typ.Memory
| pointer (typ : Typ)
| array (typ : Typ)
| struct (sym : Symbol)
deriving Inhabited, Hashable
end

namespace Typ

def Primitive.toString : Typ.Primitive → String
  | .int  => "int"
  | .bool => "bool"
instance : ToString Primitive where toString := Primitive.toString

mutual
def Memory.toString : Typ.Memory → String
  | .pointer (typ : Typ)   => s!"{toString typ}*"
  | .array (typ : Typ)     => s!"{toString typ}[]"
  | .struct (sym : Symbol) => s!"struct {sym}"

def toString : Typ → String
  | .any => "`any"
  | .prim (p : Primitive) => Primitive.toString p
  | .mem (m : Typ.Memory) => Memory.toString m
end

instance : ToString Memory where toString := Memory.toString
instance : ToString Typ where toString := Typ.toString
instance : ToString (Option Typ) where
  toString | none => "void" | some t => s!"{t}"

mutual
-- encoding structural equality
def structEq (a b : Typ) : Bool :=
  match a, b with
  | .any, .any => true
  | .prim p1, .prim p2 => p1 = p2
  | .mem m1, .mem m2 => Memory.structEq m1 m2
  | _, _ => false

def Memory.structEq (a b : Memory) : Bool :=
  match a, b with
  | .struct s1, .struct s2 => s1 = s2
  | .pointer t1, .pointer t2 => Typ.structEq t1 t2
  | .array t1, .array t2 => Typ.structEq t1 t2
  | _, _ => false
end

mutual
theorem deq {a b : Typ} : structEq a b = true ↔ a = b := by
  cases a <;> cases b <;>
  ( unfold structEq
    simp
    try apply Memory.deq
  )

theorem Memory.deq {a b : Memory} : Memory.structEq a b = true ↔ a = b := by
  cases a <;> cases b <;>
  ( unfold Memory.structEq
    simp
    try apply Typ.deq
  )
end

instance : DecidableEq Typ := fun a b =>
  match Bool.decEq (Typ.structEq a b) true with
  | .isTrue h  => .isTrue (Typ.deq.mp h)
  | .isFalse h => .isFalse (h ∘ Typ.deq.mpr)
instance : DecidableEq Memory := fun a b =>
  match Bool.decEq (Memory.structEq a b) true with
  | .isTrue h  => .isTrue (Memory.deq.mp h)
  | .isFalse h => .isFalse (h ∘ Memory.deq.mpr)

mutual
  def equiv (a b : Typ) : Bool :=
    match a, b with
    | .any, _   | _, .any  => true
    | .prim p1  , .prim p2 => p1 == p2
    | .mem m1   , .mem m2  => Memory.equiv m1 m2
    | _, _                 => false

  def Memory.equiv (a b : Memory) : Bool :=
    match a, b with
    | .pointer t1, .pointer t2 => equiv t1 t2
    | .array t1  , .array t2   => equiv t1 t2
    | .struct s1 , .struct s2  => s1 == s2
    | _, _                     => false
end

def isScalar : Typ → Bool
  | .prim .int => true
  | .prim .bool => true
  | _ => false

def isSmall : Typ → Bool
  | .mem (.struct _) => false
  | _ => true

def sizeof : Typ → Option Nat
  | .any => none
  | .prim .int => some 4
  | .prim .bool => some 1
  | .mem (.pointer _) => some 8
  | .mem (.array _) => some 8
  | .mem (.struct _) => none

structure Typed (α : Type) where
  type : Typ
  data : α
deriving Inhabited

def Typed.toString [ToString α] (a : Typed α) : String :=
  s!"({a.data} : {a.type})"
instance [ToString α] : ToString (Typed α) := ⟨Typed.toString⟩

end Typ
