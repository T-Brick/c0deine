import C0deine.Utils.Symbol

namespace C0deine

inductive Typ.Primitive
| int
| bool
deriving DecidableEq, Inhabited, Hashable

mutual
inductive Typ
| prim (p : Typ.Primitive)
| mem (m : Typ.Memory)
deriving Inhabited, Hashable

inductive Typ.Memory
| pointer (typ : Typ)
| array (typ : Typ)
| struct (sym : Symbol)
deriving Inhabited, Hashable
end

inductive Typ.Check
| type : Typ → Typ.Check
| void
| any
deriving Inhabited

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
  | .prim (p : Primitive) => Primitive.toString p
  | .mem (m : Typ.Memory) => Memory.toString m
end

def Check.toString : Check → String
  | .type t => s!"{Typ.toString t}"
  | .void => "'void"
  | .any => "'any"

instance : ToString Memory where toString := Memory.toString
instance : ToString Typ where toString := Typ.toString
instance : ToString Typ.Check where toString := Typ.Check.toString
instance : ToString (Option Typ) where
  toString | none => "void" | some t => s!"{t}"

mutual
-- encoding structural equality
def structEq (a b : Typ) : Bool :=
  match a, b with
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

deriving instance DecidableEq for Typ.Check

mutual
  def equiv (a b : Typ) : Bool :=
    match a, b with
    | .prim p1  , .prim p2    => p1 == p2
    | .mem m1   , .mem m2     => Memory.equiv m1 m2
    | _, _                    => false

  def Memory.equiv (a b : Memory) : Bool :=
    match a, b with
    | .pointer t1, .pointer t2 => equiv t1 t2
    | .array t1  , .array t2   => equiv t1 t2
    | .struct s1 , .struct s2  => s1 == s2
    | _, _                     => false
end

def Check.equiv (a b : Check) : Bool :=
  match a, b with
  | .type t1, .type t2            => Typ.equiv t1 t2
  | .void, .void                  => true
  | .any, .type (.mem (.array _))
  | .type (.mem (.array _)), .any => false
  | .any, _ | _, .any             => true
  | _, _ => false

def isScalar : Typ → Bool
  | .prim .int => true
  | .prim .bool => true
  | _ => false
def Check.isScalar : Typ.Check → Bool
  | .type t => t.isScalar
  | _ => false

def isSmall : Typ → Bool
  | .mem (.struct _) => false
  | _ => true
def Check.isSmall : Typ.Check → Bool
  | .type t => t.isSmall
  | _ => true

def sizeof : Typ → Option Nat
  | .prim .int => some 4
  | .prim .bool => some 1
  | .mem (.pointer _) => some 8
  | .mem (.array _) => some 8
  | .mem (.struct _) => none
def Check.sizeof : Typ.Check → Option Nat
  | .type t => t.sizeof
  | _ => none
end Typ
