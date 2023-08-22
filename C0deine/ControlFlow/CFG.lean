
import C0deine.Context.Label
import C0deine.ControlFlow.Digraph

namespace C0deine.ControlFlow


namespace Block
-- we track what the block came from, this is potentially useful for optimising
-- as well as generating WASM output.
inductive BlockType
| unknown
| loop
| funcEntry
| funcExit
| thenClause
| elseClause
| ternaryTrue
| ternaryFalse
| afterLoop
| afterITE
| afterTernary
| afterRet
instance : Inhabited BlockType := ⟨.unknown⟩

def BlockType.toString : BlockType → String
  | .unknown => "unknown"
  | .loop => "loop"
  -- | .loopguard => "loop-guard"
  | .funcEntry => "func-entry"
  | .funcExit => "func-exit"
  | .thenClause => "then-clause"
  | .elseClause => "else-clause"
  | .ternaryTrue => "ternary-true"
  | .ternaryFalse => "ternary-false"
  | .afterLoop => "after-loop"
  | .afterITE => "after-ifelse"
  | .afterTernary => "after-ternary"
  | .afterRet => "after-return"
instance : ToString BlockType where toString := BlockType.toString

end Block

class Block (Stmt Exit : Type) where
  label : Label
  type  : Block.BlockType
  body  : List Stmt
  exit  : Exit

instance : BEq (Block α β)      where beq x y := x.label == y.label
instance : Hashable (Block α β) where hash b := hash b.label

@[inline] def Block.loop (b : Block α β) : Bool :=
  match b.type with
  | .loop => true
  | _     => false

@[inline] def Block.after_loop (b : Block α β) : Bool :=
  match b.type with
  | .afterLoop => true
  | _          => false

structure CFG (α β : Type) where
  graph : Digraph Label
  entry : Label
  blocks : Label.Map (Block α β)
  -- todo add more things!

namespace CFG

end CFG
