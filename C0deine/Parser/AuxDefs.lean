import Megaparsec

namespace Megaparsec

open Parsec Common

local instance : Inhabited ([Monad m] → [Alternative m] → γ → (γ → m γ) → m γ) := ⟨λ g _ => pure g⟩ in
partial def foldl [Monad m] [Alternative m] (base : γ) (rightCont : γ → m γ) : m γ :=
  (do let base' ← rightCont base; foldl base' rightCont) <|> (pure base)

partial def many' {m : Type u → Type v} {℘ α β E : Type u} {γ : Type u}
                 [MonadParsec.MonadParsec m ℘ α E β] [Monad m] [Alternative m]
                 (p : m γ)
                 : m (List γ) :=
  aux []
where aux (acc) : m (List γ) :=
  (do let a ← p; aux (a::acc)) <|> pure acc.reverse

partial def sepBy {γ : Type} [MonadParsec.MonadParsec m ℘ α E β] [Monad m] [Alternative m] (p : m γ) (sep : m Unit)
  : m (Array γ) := do
  let a ← p
  foldl #[a] (fun acc =>
    (do sep; let a ← p; return acc.push a)
    <|> (pure acc)
  )

partial def dropMany [Monad m] [Alternative m] (p : m PUnit) : m PUnit := do
  (do p; dropMany p) <|> pure ⟨⟩

def getSourcePos : ParsecT m β ℘ E ParserState.SourcePos :=
  fun _ξ state _ _ (⟨⟩, f) _ => f state.posState.sourcePos state []

instance [Monad m] : MonadLift m (ParsecT m β ℘ E) where
  monadLift ma := fun _ pstate _ _ ({}, e) _ =>
    ma >>= fun a => e a pstate []

def TokenArray (α) := Array α
instance [Inhabited α] : Inhabited (TokenArray α) :=
  show Inhabited (Array α) from inferInstance

structure TokenArraySource (α) where
  source : Array (ParserState.SourcePos × α)
  index : Nat
  index_le : index ≤ source.size

def OfTokenArray (α : Type u) := α

instance [T : ToString α] : ToString (OfTokenArray α) := T
instance [O : Ord α] : Ord (OfTokenArray α) := O
instance [P : Printable.Printable α] : Printable.Printable (OfTokenArray α) := P

instance [Inhabited α] : Straume.Iterator.Iterable (TokenArray α) (OfTokenArray α) where
  push := .push
  length s := s.size
  hasNext | ⟨s, i⟩ => i < s.size
  next | ⟨s, i⟩ => if i < s.size then ⟨s, i+1⟩ else ⟨s, i⟩
  extract
    | ⟨s₁, b⟩, ⟨_, e⟩ =>
      if b > e then default
      else s₁.extract b e
  curr | ⟨s, i⟩ => (show Array _ from s)[i]!

instance [Monad m] : @Straume.Straume m (TokenArraySource α) Straume.Chunk.Chunk (TokenArray α) (OfTokenArray α) where
  take1 src _ := pure <|
    let {source,index,index_le} := src
    if h:index = source.size then (.nil, src)
    else
      have h : index < source.size := Nat.lt_of_le_of_ne index_le h
      let src' := {source, index := index+1, index_le := h}
      if index+1 < source.size then
        (.cont (source[index]'h).2, src')
      else
        (.fin ((source[index]'h).2, .eos), src')
  takeN n src _ := pure <|
    let {source,index,index_le:=_} := src
    if index = source.size then (.nil, src)
    else
      if h:index+n < source.size then
        let src' := {source, index := index+n, index_le := Nat.le_of_lt h}
        (.cont (source.toSubarray index (index+n) |>.toArray.map (·.2)), src')
      else
        let src' := {source, index := source.size, index_le := Nat.le_refl _}
        (.fin ((source.toSubarray index |>.toArray.map (·.2)), .eos), src')
  takeWhile p src _ := pure <|
    let {source,index,index_le} := src
    if h:index = source.size then (.nil, src)
    else Id.run do
      let start := index
      let mut index : Fin source.size := ⟨index, Nat.lt_of_le_of_ne index_le h⟩
      while p (source[index].2) do
        if h:index + 1 < source.size then
          index := ⟨index+1,h⟩
        else
          let src' := {source, index := source.size, index_le := Nat.le_refl _}
          return (.fin ((source.toSubarray start |>.toArray.map (·.2)), .eos), src')
      let src' := {source, index := index, index_le := Nat.le_of_lt index.isLt}
      return (.cont (source.toSubarray start index |>.toArray.map (·.2)), src')

instance : Straume.Iterator.Bijection (OfTokenArray α) (TokenArray α) where

instance : Streamable.Streamable (TokenArraySource α) where
  reachOffset offset pos :=
    -- TODO: make this not none
    (.none, {pos with offset})
