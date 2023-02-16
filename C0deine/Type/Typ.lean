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
| void_star
| any
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
  | .pointer (typ : Typ)   => s!"{Typ.toString typ} *"
  | .array (typ : Typ)     => s!"{Typ.toString typ}[]"
  | .struct (sym : Symbol) => s!"struct {sym}"

def toString : Typ → String
  | prim (p : Primitive) => Primitive.toString p
  | .mem (m : Typ.Memory) => Memory.toString m
  | .void_star => "void *"
  | .any => "'any"
end

instance : ToString Typ.Memory where toString := Typ.Memory.toString
instance : ToString Typ where toString := Typ.toString

mutual
-- encoding structural equality
def deq (a b : Typ) : Decidable (a = b) :=
  match a, b with
  | .prim p1, .prim p2 =>
    match decEq p1 p2 with
    | isTrue h  => isTrue  <| h ▸ rfl
    | isFalse h => isFalse <| fun h' => by simp at h'; apply h h'
  | .mem m1, .mem m2 =>
    match Typ.Memory.deq m1 m2 with
    | isTrue h  => isTrue  <| h ▸ rfl
    | isFalse h => isFalse <| fun h' => by simp at h'; apply h h'
  | .void_star, .void_star =>
    isTrue <| Eq.refl Typ.void_star
  | .any, .any =>
    isTrue <| Eq.refl Typ.any
  | _, _ => sorry
    -- isFalse <| fun h => _

def Memory.deq (a b : Typ.Memory) : Decidable (a = b) :=
  match a, b with
  | .struct s1, .struct s2 =>
    match decEq s1 s2 with
    | isTrue h  => isTrue  <| h ▸ rfl
    | isFalse h => isFalse <| fun h' => by simp at h'; apply h h'
  | .pointer t1, .pointer t2 =>
    match Typ.deq t1 t2 with
    | isTrue h  => isTrue  <| h ▸ rfl
    | isFalse h => isFalse <| fun h' => by simp at h'; apply h h'
  | .array t1, .array t2 =>
    match Typ.deq t1 t2 with
    | isTrue h  => isTrue  <| h ▸ rfl
    | isFalse h => isFalse <| fun h' => by simp at h'; apply h h'
  | _, _ => sorry
    -- isFalse <| _
end

instance : DecidableEq Typ.Memory := Typ.Memory.deq
instance : DecidableEq Typ := Typ.deq

mutual
  def equiv (a b : Typ) : Bool :=
    match a, b with
    | .prim p1  , .prim p2    => p1 == p2
    | .mem m1   , .mem m2     => Memory.equiv m1 m2
    | .void_star, .void_star  => true
    | .any, _ | _, .any       => true
    | _, _                    => false

  def Memory.equiv (a b : Memory) : Bool :=
    match a, b with
    | .pointer t1, .pointer t2 => equiv t1 t2
    | .array t1  , .array t2   => equiv t1 t2
    | .struct s1 , .struct s2  => s1 == s2
    | _, _                     => false
end

instance : BEq Typ where beq := equiv
instance : BEq Memory where beq := Memory.equiv

-- A type is reduced if it contains no "any"
-- todo: do we need to lookup the symbol for structures?
mutual
inductive Reduced : Typ → Prop where
| prim_int_reduced : Reduced (Typ.prim Typ.Primitive.int)
| prim_bool_reduced : Reduced (Typ.prim Typ.Primitive.bool)
| mem_reduced : ∀ m, Memory.Reduced m → Reduced (Typ.mem m)
| void_reduced : Reduced Typ.void_star

inductive Memory.Reduced : Memory → Prop where
| pointer_reduced : ∀ t, Reduced t → Memory.Reduced (Typ.Memory.pointer t)
| array_reduced   : ∀ t, Reduced t → Memory.Reduced (Typ.Memory.array t)
| struct_reduced  : ∀ s, Memory.Reduced (Typ.Memory.struct s)
end

theorem Reduced.not_any : ¬ Reduced (Typ.any) := fun h => nomatch h

def isScalar : Typ → Bool
  | .prim .int => true
  | .prim .bool => true
  | _ => false

def isSmall : Typ → Bool
  | .mem (.struct _) => false
  | _ => true

def sizeof : Typ → Option Nat
  | .prim .int => some 4
  | .prim .bool => some 1
  | .mem (.pointer _) => some 8
  | .mem (.array _) => some 8
  | .mem (.struct _) => none
  | .void_star => some 8
  | _ => none

end Typ
