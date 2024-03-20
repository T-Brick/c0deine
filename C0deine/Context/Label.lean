/- C0deine - Label
   Utilities for generating fresh labels.
   - Thea Brick
 -/
import Std
import Wasm.Text.Ident

namespace C0deine

structure Label where
  id : Nat
  name : Option String
deriving DecidableEq, Inhabited

namespace Label

@[inline] def toString (l : Label) : String :=
  match l.name with
  | none => s!"L{l.id}"
  | some name => name

instance : ToString Label := ⟨toString⟩
instance : Repr Label := ⟨fun l _ => toString l⟩
instance : Ord Label where compare l1 l2 := Ord.compare l1.id l2.id
instance : Hashable Label where hash l := hash l.id


def main   : Label := ⟨0, "main"⟩
def calloc : Label := ⟨1, "calloc"⟩
def free   : Label := ⟨2, "free"⟩
def abort  : Label := ⟨3, "abort"⟩
def error  : Label := ⟨4, "error"⟩
def debug  : Label := ⟨5, "debug"⟩

def startId := 6

@[inline, reducible] def Map (α : Type) := Std.HashMap Label α

def toWasmIdent (l : Label) : Wasm.Text.Ident :=
  { name := toString l
  , name_nonempty    := by sorry
  , name_valid_chars := by sorry
  }

def toWasmLoopBreak (l : Label) : Wasm.Text.Ident :=
  { name := toString l ++ "_break"
  , name_nonempty    := by sorry
  , name_valid_chars := by sorry
  }

end Label
