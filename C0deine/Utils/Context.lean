import Std
import C0deine.Utils.Temp
import C0deine.Utils.Label
import C0deine.Utils.Symbol

namespace C0deine

structure Context.State where
  nextTemp : Temp
  nextLabel : Label
  nextSymbolId : UInt64
  symbolCache : Std.HashMap String Symbol

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

namespace Symbol

def symbol (name : String) : Context Symbol :=
  fun s =>
    match s.symbolCache.find? name with
    | some sym => (sym, s)
    | none =>
      let id := s.nextSymbolId
      let sym : Symbol := ⟨name, id⟩
      (sym, {s with nextSymbolId := s.nextSymbolId + 1
                    symbolCache  := s.symbolCache.insert name sym
      })

end Symbol

