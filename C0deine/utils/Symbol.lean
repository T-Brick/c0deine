import Std

namespace C0deine

structure Symbol where
  name : String
  id : Nat
deriving DecidableEq, Inhabited

instance : ToString Symbol where toString | s => s.name
