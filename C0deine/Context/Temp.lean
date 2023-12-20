/- C0deine - Temp
   Utilities for creating fresh temps.
   - Thea Brick
 -/
import Std
import C0deine.Utils.ValueSize
import Wasm.Text.Ident

namespace C0deine

def Temp := Nat
deriving DecidableEq, Inhabited, Hashable

namespace Temp

instance : ToString Temp where
  toString | t => s!"%t{show Nat from t}"

-- reserved temps (useful for WASM)
def general : Temp := (0:) -- general purpose
def index   : Temp := (1:) -- indexing into arrays

def startId := 2

def toNat (t : Temp) : Nat := t
def toUInt64 : Temp → UInt64 := Nat.toUInt64

def Map (α : Type) := Std.HashMap Temp α
def Map.empty : Map α := Std.HashMap.empty

def toWasmIdent (temp : Temp) : Wasm.Text.Ident :=
  { name := s!"t{show Nat from temp}"
  , name_nonempty := by sorry
  , name_valid_chars := by sorry
  }

end Temp

@[reducible] def SizedTemp := Sized Temp
deriving DecidableEq

def SizedTemp.temp (stemp : SizedTemp) : Temp := stemp.data
def SizedTemp.toString (stemp : SizedTemp) : String :=
  s!"%t{stemp.size}{show Nat from stemp.temp}"
instance : ToString SizedTemp := ⟨SizedTemp.toString⟩

def SizedTemp.toWasmIdent (stemp : SizedTemp) : Wasm.Text.Ident :=
  { name := s!"t{stemp.size}{show Nat from stemp.temp}"
  , name_nonempty := by sorry
  , name_valid_chars := by sorry
  }
