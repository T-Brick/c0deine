import Std
import Wasm.Text.Ident

namespace C0deine

structure Label where
  id : Nat
  name : Option String
deriving DecidableEq, Inhabited

namespace Label

instance : ToString Label where
  toString l :=
    match l.name with
    | none => s!"L{l.id}"
    | some name => name
instance : Ord Label where compare l1 l2 := Ord.compare l1.id l2.id
instance : Hashable Label where hash l := hash l.id


def main   : Label := ⟨0, "main"⟩
def calloc : Label := ⟨1, "calloc"⟩
def abort  : Label := ⟨2, "abort"⟩
def fpe    : Label := ⟨3, "sigfpe"⟩
def memerr : Label := ⟨4, "sigusr2"⟩

def startId := 5

@[reducible] def Map (α : Type) := Std.HashMap Label α

def toWasmIdent (l : Label) : Wasm.Text.Ident :=
  { name := toString l
  , name_nonempty := by sorry
  , name_valid_chars := by sorry
  }

end Label
