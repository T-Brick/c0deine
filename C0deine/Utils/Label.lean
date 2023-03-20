import Std

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
instance : Hashable Label where hash l := hash l.id

def Label.main : Label := ⟨0, "main"⟩
def Label.calloc : Label := ⟨1, "calloc"⟩

def Map (α : Type) := Std.HashMap Label α

end Label
