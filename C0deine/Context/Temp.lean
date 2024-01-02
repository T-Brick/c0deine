/- C0deine - Temp
   Utilities for creating fresh temps.
   - Thea Brick
 -/
import Std
import C0deine.Utils.ValueSize
import Wasm.Text.Ident

namespace C0deine

structure Temp where
  id : Nat
  name : Option String
deriving DecidableEq, Inhabited, Hashable

namespace Temp

def toRawString (t : Temp) : String :=
  match t.name with
  | none => s!"t{t.id}"
  | some n => s!"t{t.id}_{n}"

instance : ToString Temp where
  toString | t => "%" ++ t.toRawString

-- reserved temps (useful for WASM)
def general : Temp := ⟨0, none⟩ -- general purpose
def index   : Temp := ⟨1, none⟩ -- indexing into arrays

def startId := 2

def toNat : Temp → Nat := Temp.id
def toUInt64 : Temp → UInt64 := Nat.toUInt64 ∘ Temp.id

def Map (α : Type) := Std.HashMap Temp α
def Map.empty : Map α := Std.HashMap.empty

def toWasmIdent (temp : Temp) : Wasm.Text.Ident :=
  { name := temp.toRawString
  , name_nonempty := by sorry
  , name_valid_chars := by sorry
  }

end Temp

@[reducible] def SizedTemp := Sized Temp
deriving DecidableEq

def SizedTemp.temp (stemp : SizedTemp) : Temp := stemp.data
def SizedTemp.toString (stemp : SizedTemp) : String :=
  s!"{stemp.temp}^{stemp.size}"
instance : ToString SizedTemp := ⟨SizedTemp.toString⟩

def SizedTemp.toWasmIdent (stemp : SizedTemp) : Wasm.Text.Ident :=
  { name := s!"{stemp.temp.toRawString}^{stemp.size}"
  , name_nonempty := by sorry
  , name_valid_chars := by sorry
  }
