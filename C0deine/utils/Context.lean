import C0deine.Utils.Temp
import C0deine.Utils.Label

namespace C0deine

structure Context.State where
  nextTemp : Temp
  nextLabel : Label

def Context := StateM Context.State

instance : Monad Context := show Monad (StateM _) from inferInstance

namespace Temp

def fresh : Context Temp :=
  fun s => (s.nextTemp, {s with nextTemp := (show Nat from s.nextTemp) + 1})

end Temp

namespace Label

def fresh : Context Label :=
  fun s => (s.nextLabel, {s with nextLabel := (show Nat from s.nextLabel) + 1})

end Label

