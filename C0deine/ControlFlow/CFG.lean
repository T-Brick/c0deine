/- C0deine - CFG
   Expands on the ControlFlow CFG implementation by keeping track of block
   information so that we can just use labels as the node representation.
   - Thea Brick
 -/
import C0deine.Context.Label
import ControlFlow.Graphs.FuncGraph
import ControlFlow.Graphs.CFG
import ControlFlow.Dominator

open ControlFlow
open ControlFlow.Digraph

namespace C0deine.ControlFlow

namespace Block
-- we track what the block came from, this is potentially useful for optimising
-- as well as generating WASM output.
inductive BlockType
| unknown
| loop
| loopguard
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
  | .loopguard => "loop-guard"
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
deriving Inhabited

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

instance : Digraph Label FuncGraphType := FuncGraph
structure C0_CFG (α β : Type) extends CFG Label FuncGraphType where
  name : Label
  blocks : Label.Map (Block α β)

-- todo move this to ControlFlow lib?
abbrev Dom.Frontier := Label → Std.HashSet Label
abbrev Dom.Tree := Std.HashMap Label (Std.HashSet Label)

structure C0_CFG.DomInfo where
  sdom : Label → Std.HashSet Label
  dom : Label → Std.HashSet Label
  sdom_by : Label → Std.HashSet Label
  idom : Label → Option Label
  frontier : Dom.Frontier
  dom_tree : Dom.Tree

open ControlFlow.Dom.Algorithm in
nonrec def C0_CFG.DomInfo.compute (cfg : C0_CFG α β)
    : Option DomInfo := do
  let ⟨sdom, dom, sdom_by⟩ ← compute cfg.toCFG
  let idom := get_immediate_dominator ⟨sdom, dom, sdom_by⟩
  let frontier ← get_dominance_frontier cfg.toCFG idom

  let block_labels := cfg.blocks.keys
  let dom_tree : Dom.Tree := block_labels.foldl (fun tree l₁ =>
    match idom l₁ with
    | .none => tree
    | .some l₂ => tree.insert l₂ (tree.getD l₂ {} |>.insert l₁)
  ) {}

  return ⟨sdom, dom, sdom_by, idom, frontier, dom_tree⟩

def Block.toString [ToString α] [ToString β] (b : Block α β) :=
  let body := b.body.map (fun stmt => s!"\t{stmt}\n") |> String.join
  s!"{b.label}:\t\t{b.type}\n{body}\t{b.exit}"
instance [ToString α] [ToString β] : ToString (Block α β) := ⟨Block.toString⟩

def C0_CFG.toString (cfg : C0_CFG α β) : String :=
  s!"#--- begin {cfg.name} ---#\n{cfg.toCFG}\n#--- end {cfg.name} ---#"
instance : ToString (C0_CFG α β) := ⟨C0_CFG.toString⟩
instance : ToString (List (C0_CFG α β)) :=
  ⟨fun cfgs => String.intercalate "\n\n" (cfgs.map ToString.toString)⟩
