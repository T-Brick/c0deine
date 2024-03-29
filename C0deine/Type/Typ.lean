/- C0deine - Typ
   Representation of C0 types that can be used across IRs.
   - Thea Brick
 -/
import C0deine.AuxDefs
import C0deine.Context.Symbol

namespace C0deine

inductive Typ.Primitive
| int
| bool
| char
| string
deriving DecidableEq, Inhabited, Hashable

mutual
inductive Typ
| any
| prim (p : Typ.Primitive)
| mem (m : Typ.Memory)
deriving DecidableEq, Inhabited, Hashable

inductive Typ.Memory
| pointer (typ : Typ)
| array (typ : Typ)
| struct (sym : Symbol)
deriving DecidableEq, Inhabited, Hashable
end

namespace Typ

def Primitive.toString : Typ.Primitive → String
  | .int    => "int"
  | .bool   => "bool"
  | .char   => "char"
  | .string => "string"
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
  @[reducible] def equiv (a b : Typ) : Bool :=
    match a, b with
    | .any, _   | _, .any  => true
    | .prim p1  , .prim p2 => p1 == p2
    | .mem m1   , .mem m2  => Memory.equiv m1 m2
    | _, _ => false

  @[reducible] def Memory.equiv (a b : Memory) : Bool :=
    match a, b with
    | .pointer t1, .pointer t2 => equiv t1 t2
    | .array t1  , .array t2   => equiv t1 t2
    | .struct s1 , .struct s2  => s1 == s2
    | _, _ => false
end

mutual
@[simp] theorem equiv_refl : ∀ τ, equiv τ τ := by
  intro τ; cases τ <;> simp [equiv]; next m => exact Memory.equiv_refl m

@[simp] theorem Memory.equiv_refl : ∀ τ, Memory.equiv τ τ := by
  intro τ; cases τ <;> simp [Memory.equiv]
  case pointer τ' => exact equiv_refl τ'
  case array τ'   => exact equiv_refl τ'
end

@[inline] def flattenOpt : Option Typ → Typ
  | none   => .any
  | some τ => τ

def isScalar : Typ → Bool
  | .prim .int => true
  | .prim .bool => true
  | .prim .char => true
  | _ => false

def isSmall : Typ → Bool
  | .mem (.struct _) => false
  | _ => true

def sizeof : Typ → Option Nat
  | .any              => none
  | .prim .int        => some 4
  | .prim .bool       => some 1
  | .prim .char       => some 1
  | .prim .string     => some 8
  | .mem (.pointer _) => some 8
  | .mem (.array _)   => some 8
  | .mem (.struct _)  => none

def sizeof! : Typ → Nat
  | .any              => 8
  | .prim .int        => 4
  | .prim .bool       => 1
  | .prim .char       => 1
  | .prim .string     => 8
  | .mem (.pointer _) => 8
  | .mem (.array _)   => 8
  | .mem (.struct _)  => 8

def is_eqtype : Typ → Bool
  | .prim .string => false
  | .mem (.struct _) => false
  | _ => true

-- todo: types must be equivalent
def intersect (t1 : Typ) (t2 : Typ) : Typ :=
  match t1, t2 with
  | .mem (.pointer t1'), .mem (.pointer t2') =>
    (.mem ∘ .pointer) (intersect t1' t2')
  | .mem (.array t1'), .mem (.array t2') =>
    (.mem ∘ .array) (intersect t1' t2')
  | .any, _ => t2
  | _, .any => t1
  | _, _    => t1

namespace Notation

scoped notation:50 "int"         => Typ.prim Typ.Primitive.int
scoped notation:50 "bool"        => Typ.prim Typ.Primitive.bool
scoped notation:50 "char"        => Typ.prim Typ.Primitive.char
scoped notation:50 "string"      => Typ.prim Typ.Primitive.string
scoped notation:50 "any"         => Typ.any
scoped notation:50 "any" "*"     => Typ.mem (Typ.Memory.pointer Typ.any)
scoped notation:50 τ:51 "*"      => Typ.mem (Typ.Memory.pointer τ)
scoped notation:50 τ:51 "[]"     => Typ.mem (Typ.Memory.array τ)
scoped notation:50 "struct" τ:51 => Typ.mem (Typ.Memory.struct τ)

end Notation

inductive Typed (α : Type) where
| mk : (type : Typ) → (data : α) → Typed α
deriving Inhabited, DecidableEq

@[reducible, simp] def Typed.data : Typed α → α   | .mk _ data => data
@[reducible, simp] def Typed.type : Typed α → Typ | .mk type _ => type

def Typed.toProd : Typed α → α × Typ
  | .mk τ a => (a, τ)

def Typed.toMap [DecidableEq α] : List (Typed α) → α → Option Typ :=
  List.toMap ∘ .map toProd

def Typed.toString [ToString α] (a : Typed α) : String :=
  s!"({a.data} : {a.type})"
instance [ToString α] : ToString (Typed α) := ⟨Typed.toString⟩

end Typ
