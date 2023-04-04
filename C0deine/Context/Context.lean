import Std
import C0deine.Context.Temp
import C0deine.Context.Label
import C0deine.Context.Symbol

namespace C0deine

structure Context.State where
  nextTemp : Temp
  nextLabel : Label
  nextSymbolId : UInt64
  symbolCache : Std.HashMap String Symbol

def Context.State.new : Context.State where
  nextTemp := (1:)
  nextLabel := ⟨Label.startId, none⟩
  nextSymbolId := 1
  symbolCache := Std.HashMap.empty.insert Symbol.main.name Symbol.main

def Context := StateM Context.State

instance : Monad Context := show Monad (StateM _) from inferInstance

namespace Temp

def fresh : Context Temp :=
  fun s => (s.nextTemp, {s with nextTemp := (show Nat from s.nextTemp) + 1})

end Temp

namespace Label

def fresh : Context Label :=
  fun s => (s.nextLabel, {s with nextLabel := ⟨s.nextLabel.id + 1, none⟩})
def namedFresh (name : String) : Context Label :=
  fun s =>
    ( {s.nextLabel with name := some name}
    , {s with nextLabel := ⟨s.nextLabel.id + 1, none⟩}
    )

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

