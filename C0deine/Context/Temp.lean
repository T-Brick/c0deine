/- C0deine - Temp
   Utilities for creating fresh temps.
   - Thea Brick
 -/
import Batteries
import C0deine.Utils.ValueSize
import Wasm.Text.Ident

namespace C0deine

structure Temp where
  id : Nat
  name : Option String
  ssa_number : Option Nat := .none
deriving DecidableEq, Inhabited, Hashable

namespace Temp

@[inline] def toRawString (t : Temp) : String :=
  match t.name, t.ssa_number with
  | .none, .none => s!"t{t.id}"
  | .some n, .none => s!"t{t.id}_{n}"
  | .none, .some m => s!"t{t.id}{m.toSubscriptString}"
  | .some n, .some m => s!"t{t.id}_{n}{m.toSubscriptString}"

@[inline] def toString (t : Temp) : String := "%" ++ t.toRawString

instance : ToString Temp := ⟨toString⟩
instance : Repr Temp := ⟨fun t _ => toString t⟩

-- reserved temps (useful for WASM)
def general : Temp := { id := 0, name := .none } -- general purpose
def index   : Temp := { id := 1, name := .none } -- indexing into arrays

def startId := 2

def toNat : Temp → Nat := Temp.id
def toUInt64 : Temp → UInt64 := Nat.toUInt64 ∘ Temp.id

def Map (α : Type) := Std.HashMap Temp α
def Map.empty : Map α := Std.HashMap.emptyWithCapacity

def toWasmIdent (temp : Temp) : Wasm.Text.Ident :=
  let temp := { temp with ssa_number := .none }
  { name := temp.toRawString
  , name_nonempty := by
      simp only [toRawString, Nat.toString_eq_repr, ne_eq]
      cases temp.name
      <;> cases temp.ssa_number
      <;> simp only [String.append_eq_empty_iff, Nat.repr_ne_empty, and_false,
                     false_and, not_false_eq_true]
  , name_valid_chars := by sorry
  }

end Temp

@[reducible] def SizedTemp := Sized Temp
deriving DecidableEq

@[inline] def SizedTemp.show_size_in_string := false
@[inline] def SizedTemp.temp (stemp : SizedTemp) : Temp := stemp.data
@[inline] def SizedTemp.toString (stemp : SizedTemp) : String :=
  if show_size_in_string
  then s!"{stemp.temp}^{stemp.size}"
  else stemp.temp.toString
instance : ToString SizedTemp := ⟨SizedTemp.toString⟩
instance : Repr SizedTemp := ⟨fun st _ => SizedTemp.toString st⟩

def SizedTemp.toWasmIdent (stemp : SizedTemp) : Wasm.Text.Ident :=
  let temp := { stemp.temp with ssa_number := .none }
  { name := s!"{temp.toRawString}^{stemp.size}"
  , name_nonempty := fun h₁ => by
      have := String.append_eq_empty_iff.mp h₁
        |>.left
        |> String.append_eq_empty_iff.mp
        |>.right
      contradiction
  , name_valid_chars := by sorry
  }
