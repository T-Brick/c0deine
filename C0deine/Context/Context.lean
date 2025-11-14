/- C0deine - Context
   A standardised context that can be used when fresh labels/symbols/temps need
   to be generated.
   - Thea Brick
   - James Gallicchio
 -/
import Batteries
import C0deine.Context.Temp
import C0deine.Context.Label
import C0deine.Context.Symbol

namespace C0deine

-- this is kinda hacky but allows us to derive Repr for the context
instance : Repr (Std.HashMap String Symbol) :=
  ⟨fun m => reprPrec m.toArray⟩

structure Context.State where
  nextTemp     : Temp
  nextLabel    : Label
  nextSymbolId : UInt64
  inLineAnno   : Option Bool -- none if annotations aren't allow
  symbolCache  : Std.HashMap String Symbol
deriving Repr, Inhabited

def Context.State.new (annotations : Bool) : Context.State where
  nextTemp     := ⟨Temp.startId, none⟩
  nextLabel    := ⟨Label.startId, none⟩
  nextSymbolId := 1
  inLineAnno   := if annotations then .some false else .none
  symbolCache  := Std.HashMap.emptyWithCapacity.insert Symbol.main.name Symbol.main

def Context := StateM Context.State

instance : Monad Context := show Monad (StateM _) from inferInstance

def Context.allowAnno : Context Bool :=
  fun s => (s.inLineAnno.isSome, s)
def Context.inLineAnno : Context Bool :=
  fun s => (s.inLineAnno.getD false, s)
def Context.setInLineAnno (b : Bool) : Context Unit :=
  fun s =>
    ((), if s.inLineAnno.isNone then s else { s with inLineAnno := .some b })

namespace Temp

def fresh : Context Temp :=
  fun s => (s.nextTemp, {s with nextTemp := ⟨s.nextTemp.id + 1, none⟩})

def namedFresh (name : String): Context Temp :=
  fun s => ( {s.nextTemp with name := some name}
           , {s with nextTemp := ⟨s.nextTemp.id + 1, none⟩}
           )

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
    match s.symbolCache.get? name with
    | some sym => (sym, s)
    | none =>
      let id := s.nextSymbolId
      let sym : Symbol := ⟨name, id⟩
      (sym, {s with nextSymbolId := s.nextSymbolId + 1
                    symbolCache  := s.symbolCache.insert name sym
      })

end Symbol
