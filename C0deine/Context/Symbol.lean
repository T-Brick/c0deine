import Std

namespace C0deine

structure Symbol where
  name : String
  id : UInt64
deriving DecidableEq, Inhabited, Repr

instance : ToString Symbol where toString s := s.name
instance : Hashable Symbol where hash s := hash s.id
instance : Ord Symbol where compare s1 s2 := Ord.compare s1.id s2.id

def Symbol.main : Symbol := ⟨"main", 0⟩

def Symbol.Map (α : Type) := Std.HashMap Symbol α
