import C0deine.AuxDefs
import C0deine.Utils.CliFormat

namespace C0deine.Parser

structure AsciiPos (s : ByteArray) where
  pos : Nat
  h_pos : pos ≤ s.size
deriving Repr

namespace AsciiPos

instance : Inhabited (AsciiPos s) := ⟨⟨0, Nat.zero_le _⟩⟩

nonrec def compare (p1 p2 : AsciiPos s) := compare p1.pos p2.pos

instance : Ord (AsciiPos s) := ⟨compare⟩
instance : DecidableEq (AsciiPos s) :=
  fun a b => by cases a; cases b; simp; exact inferInstance
instance : LE (AsciiPos s) := ⟨(·.pos ≤ ·.pos)⟩
instance : DecidableRel (LE.le (α := AsciiPos s)) :=
  fun a b => by simp [LE.le]; exact inferInstance
instance : LT (AsciiPos s) := ⟨(·.pos < ·.pos)⟩
instance : DecidableRel (LT.lt (α := AsciiPos s)) :=
  fun a b => by simp [LT.lt]; exact inferInstance

def atEnd (p : AsciiPos s) : Bool := p.pos = s.size
def get (p : AsciiPos s) (h : ¬p.atEnd := by assumption) : UInt8 :=
  have : p.pos < s.size := Nat.lt_of_le_of_ne p.h_pos (by
    simp [atEnd] at h; exact h)
  s[p.pos]
def next (p : AsciiPos s) (h : ¬p.atEnd := by assumption) : AsciiPos s :=
  have : p.pos < s.size := Nat.lt_of_le_of_ne p.h_pos (by
    simp [atEnd] at h; exact h)
  { pos := p.pos+1, h_pos := this}

end AsciiPos


def ParserT.State.lineIndices (s : ByteArray) : Array (AsciiPos s) := Id.run do
  let mut lines := #[⟨0, Nat.zero_le _⟩]
  for h:i in [0:s.size] do
    if s[i]'h.2 = '\n'.toUInt8 then
      lines := lines.push ⟨i+1, h.2⟩
  return lines

structure ParserT.State (s : ByteArray) where
  lines : ThunkCache (fun () => State.lineIndices s)
  pos : AsciiPos s
deriving Inhabited

namespace ParserT.State

-- binary search for which line a position occurs in
def getPosLine (state : State s) : Fin state.lines.val.get.size :=
  let lines := state.lines.val.get
  have : lines.size > 0 := sorry
  have : lines.size-1 < lines.size := Nat.sub_lt (this) (by decide)
  if hlo:lines[0] ≤ state.pos then
    if hhi:state.pos < lines[lines.size-1] then
      aux lines state.pos ⟨0, by assumption⟩ ⟨lines.size-1,this⟩
        (Nat.zero_le _) hlo hhi
    else ⟨lines.size-1, by assumption⟩
  else ⟨0, by assumption⟩
where aux lines tgt (lo hi : Fin lines.size) (h : lo ≤ hi)
      (hlo : lines[lo] ≤ tgt) (hhi : tgt < lines[hi]) :=
  if h':lo = hi then lo
  else
    have : lo < hi := Nat.lt_of_le_of_ne h (by intro; apply h'; cases lo; cases hi; simp at *; assumption)
    let mid := (lo.val + hi.val) / 2
    have : lo.val ≤ mid := by
      apply Nat.le_div_iff_mul_le (by decide) |>.mpr
      simp [Nat.mul_succ]; apply Nat.add_le_add (Nat.le_refl _)
      apply Nat.le_of_lt; assumption
    have : mid < hi.val := by
      apply Nat.div_lt_iff_lt_mul (by decide) |>.mpr
      simp [Nat.mul_succ]; apply Nat.add_lt_add_right
      cases lo; cases hi; assumption
    have : mid < lines.size := Nat.lt_trans this hi.isLt
    let mid : Fin _ := ⟨mid,this⟩
    if lo = mid then
      mid
    else
    match _h:compare lines[mid] tgt with
    | .eq => mid
    | .lt =>
      have : hi.val - mid.val < hi.val - lo.val := sorry
      aux lines tgt mid hi sorry sorry sorry
    | .gt =>
      have : mid.val - lo.val < hi.val - lo.val := sorry
      aux lines tgt lo mid sorry sorry sorry
termination_by aux lo hi _ _ _ => hi.val - lo.val

def getPosLineCol (state : State s) :=
  let line := getPosLine state
  let col := state.pos.pos - state.lines.val.get[line].pos
  (line,col)

def getLines (state : State s) (fr to : Fin state.lines.val.get.size) : String :=
  let fr : AsciiPos _ := state.lines.val.get[fr]
  let to : AsciiPos _ :=
    if h:to+1 < state.lines.val.get.size then
      ⟨state.lines.val.get[to.val+1].pos - 1, by
        apply Nat.le_trans
        . apply Nat.sub_le
        . generalize h : (Thunk.get state.lines.val)[_ + 1] = e
          apply e.h_pos⟩
    else
      ⟨s.size, Nat.le_refl _⟩
  s.extract fr.pos to.pos |> String.fromUTF8Unchecked

end ParserT.State


structure ParserT.Error (s) where
  expected : List String
  stack : List (String × AsciiPos s)
deriving Inhabited, Repr

namespace ParserT.Error

def addStack (name : String) (pos : AsciiPos s) : ParserT.Error s → ParserT.Error s
| { expected, stack } => { expected, stack := (name, pos)::stack }

def headToks : ParserT.Error s → List String
| { expected, stack := [] } => expected
| { expected := _, stack := (head,_)::_ } => [head]

def formatPretty (state : State s) (e : ParserT.Error s) : String :=
  let (line, col) := state.getPosLineCol
  let ctxStart : Fin _ := ⟨line.val-2, Nat.lt_of_le_of_lt (Nat.sub_le _ _) line.isLt⟩
  let ctxWidth := 80
  let ctxLeftOff := if col ≤ 60 then 0 else min 4 (col-60)

  open Utils CliFormat in
  let context :=
    let rawLines : Rect := state.getLines ctxStart line
    let offset :=
      if ctxLeftOff > 0 then
        hbox [" ...", rawLines.dropLeft ctxLeftOff] (align := .bottom)
      else rawLines

    hbox (align := .top) [
      -- line numbers
      hbox (sep := [" |"]) [
        vbox (align := .right)
          (List.range' (ctxStart.val+1) (line.val-ctxStart.val+1) |>.map (toString ·))
      , empty]
      -- actual context
    , vbox [
        offset.trimWidth ctxWidth
      , "".pushn ' ' (col - ctxLeftOff) ++ "^" ]
    ]

  let expected :=
    match e.expected with
    | [] => "Unexpected input"
    | es => "Expected " ++ String.intercalate " OR " es
  let stack :=
    e.stack.reverse.map (fun (c,pos) =>
      let (line, col) := {state with pos}.getPosLineCol
      s!"  at {line.val+1}:{col} {c}")
    |> String.intercalate "\n"
  vbox [
    s!"Parse error at {line.val+1}:{col}"
  , context
  , expected
  , stack
  ]

end ParserT.Error

def ParserT (m s α) := ExceptT (Unit → ParserT.Error s) (StateT (ParserT.State s) m) α

namespace ParserT

variable [Monad m]

instance : Inhabited (ParserT m s α) := ⟨fun _ => pure default⟩

instance : Monad (ParserT m s) :=
  show Monad (ExceptT _ _) from inferInstance
instance : MonadStateOf (ParserT.State s) (ParserT m s) :=
  show MonadStateOf _ (ExceptT _ _) from inferInstance

instance : MonadLift m (ParserT m s) where
  monadLift m := fun s => do return (.ok (← m), s)

nonrec def run (s : ByteArray) (p : ParserT m s α) :=
  p.run { lines := .new, pos := ⟨0, Nat.zero_le _⟩ }

@[inline] def getPos : ParserT m s (AsciiPos s) :=
  do return (← get).pos

@[inline] def setPos (p : AsciiPos s) : ParserT m s Unit :=
  do set { (← get) with pos := p}

@[inline] def throwExpected (es : Unit → List String) : ParserT m s α :=
  fun s => pure (.error (fun () => { expected := es (), stack := [] }), s)

@[inline] def throwUnexpected : ParserT m s α := throwExpected (fun () => [])

@[inline] def withContext (name : String) (p : ParserT m s α) : ParserT m s α :=
  fun s => do
  match ← p s with
  | (.ok a    , s') =>
    return (.ok a, s')
  | (.error e , s') =>
    return (.error <| fun () => (e ()).addStack name s.pos, s')

@[inline] def eof : ParserT m s Unit := do
  let p ← getPos
  if p.atEnd then
    return
  else
    throwExpected fun () => ["<eof>"]

@[inline] def any : ParserT m s UInt8 := do
  let p ← getPos
  if h : p.atEnd then
    throwExpected fun () => ["<any-char>"]
  else
  setPos p.next
  return p.get

@[inline] def withBacktracking (p : ParserT m s α) : ParserT m s α :=
  fun s => do
  match ← p s with
  | (.ok a, s')   => return (.ok a, s')
  | (.error e, _) => return (.error e, s)

@[inline] def atomically (p : ParserT m s α) (name : Option String := none) : ParserT m s α :=
  fun s => do
  match ← p s with
  | (.ok a, s')   => return (.ok a, s')
  | (.error _, _) => throwExpected (fun () => name.toList) s

@[inline] def notFollowedBy (p : ParserT m s α) : ParserT m s Unit :=
  fun s => do
  match ← p s with
  | (.ok _, _) =>
    throwUnexpected s
  | (.error _, _) =>
    return (.ok (), s)

@[inline] def guard (b : Bool) : ParserT m s Unit := do
  if b then return else throwUnexpected

@[inline] def or (p1 p2 : ParserT m s α) : ParserT m s α :=
  fun state => do
  match ← p1 state with
  | (.ok a, state') => return (.ok a, state')
  | (.error e, state') =>
  if state.pos ≠ state'.pos then
    return (.error e, state')
  else
  match ← p2 state with
  | (.ok a, state') =>
    return (.ok a, state')
  | (.error e2, state') =>
  if state.pos ≠ state'.pos then
    return (.error e2, state')
  else
    throwExpected (fun () => (e ()).headToks ++ (e2 ()).headToks) state 

instance : OrElse (ParserT m s α) where
  orElse p q := or p (q ())

@[inline] def withBacktrackingUntil (p : ParserT m s α) (q : α → ParserT m s β) : ParserT m s β :=
  fun state => do
  match ← p state with
  | (.error e, _) =>
    return (.error e, state)
  | (.ok a, state') =>
  match ← q a state' with
  | (.error e, state'') =>
    if state'.pos = state''.pos then
      return (.error e, state)
    else
      return (.error e, state'')
  | (.ok b, state'') =>
    return (.ok b, state'')

@[inline] def first (ps : List (ParserT m s α)) (h : ps ≠ [] := by simp) :=
  match ps with
  | [] => by contradiction
  | p::ps => ps.foldl or p

@[inline] def foldl (p : ParserT m s α) (q : α → ParserT m s α) : ParserT m s α := do
  let a ← p
  let pos ← getPos
  aux pos a
where @[inline] aux pos a := do
  (do
    let a ← q a
    let pos' ← getPos
    if h:pos < pos' then
      have : s.size - pos'.pos < s.size - pos.pos :=
        Nat.sub_lt_sub_left
          (Nat.lt_of_lt_of_le h pos'.h_pos)
          h
      aux pos' a
    else
      panic! "backtracked in foldl")
  <|> (return a)
termination_by aux p _ => s.size - p.pos

@[inline] def dropMany (p : ParserT m s Unit) : ParserT m s Unit :=
  foldl (return ()) (fun () => p)

@[inline] def sepBy (sep : ParserT m s Unit) (p : ParserT m s α) : ParserT m s (Array α) :=
  (do let a ← p
      foldl (return #[a]) (fun acc => do
        let a ← withBacktrackingUntil sep (fun () => p)
        return acc.push a))
  <|> (return #[])

@[inline] def option (p : ParserT m s α) : ParserT m s (Option α) :=
  (do let a ← p; return some a)
  <|> (return none)

/-@[inline] def fix (p : ParserT m s (α → α)) (q : ParserT m s α) : ParserT m s α :=
  fun s => aux s
where aux state := do
  match ← p state with
  | (.error e, state') => return (.error e, state')
  | (.ok f, state') =>
  if h:state.pos < state'.pos then
    have : s.size - state'.pos.pos < s.size - state.pos.pos :=
      Nat.sub_lt_sub_left
        (Nat.lt_of_lt_of_le h state'.pos.h_pos)
        h
    match ← aux state' with
    | (.error e, state'') => return (.error e, state'')
    | (.ok a, state'') =>
    return (f a, state'')
  else
    panic! "backtracked in fix"
termination_by aux state => s.size - state.pos.pos
-/

@[inline] def char (c : Char) : ParserT m s Unit :=
  atomically (name := c.toString) <| do
  let c' ← any
  guard (c = c')

@[inline] def charMatching (p : Char → Bool) : ParserT m s Char :=
  withBacktracking (do
  let c ← any
  guard (p c)
  return c)

@[inline] def string (s : String) : ParserT m src Unit :=
  let L := s.toList
  do aux L (← getPos)
where aux L p := do
  match L with
  | [] =>
    return ()
  | x::xs =>
    char x
    aux xs p

@[inline] def wholeString (s : String) : ParserT m src Unit :=
  withBacktracking (string s)