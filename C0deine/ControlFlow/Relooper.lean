/- C0deine - Relooper
   We use the "Relooper Algorithm" to reconstruct more structured control-flow
   from our less structured basic blocks. While it might be simpler to go from
   a language that represent's C0 control-flow better (like the TST), this would
   make it hard to do many optimisations and run other checks that C0 requires.

   In theory, the code generated via this algorithm shouldn't be too inefficient
   since C0 doesn't have strange control-flow (like goto).

   https://github.com/emscripten-core/emscripten/blob/main/docs/paper.pdf

  In future, we should be able to not use this algorithm by using dominators to
  identify forward and backward edges, which immediately identifies the loop
  structure in the graph. For now this works.

  - Thea Brick
-/
import C0deine.Context.Label
import C0deine.ControlFlow.CFG
import ControlFlow.FindPath

namespace C0deine.ControlFlow.Relooper

open ControlFlow
open ControlFlow.Digraph
open ControlFlow.Path.Find

/- The Shape is what is outputted by relooper and is the identified structure
 -   of the control flow graph.
 - `simple` represents block with only one exit
 - `loop`   represents a block body and the block after the loop
 - `multi`  represents branching and then the block after they merge
 -/
inductive Shape where
| simple : Label → Option Shape → Shape
| loop   : (inner next : Option Shape) → Shape
| multi  : (left right next : Option Shape) → Shape
| illegal : List Label → Shape

/- These functions are useful for when trying to build the WASM output given
   the shape.
 -/
def Shape.getLabels : Shape → List Label
  | .simple lbl _         => [lbl]
  | .loop .none _         => []
  | .loop (.some inner) _ => getLabels inner
  | .multi left right _   =>
    match left, right with
    | .none  , .none   => []
    | .some l, .none   => getLabels l
    | .none  , .some r => getLabels r
    | .some l, .some r => getLabels l ++ getLabels r
  | .illegal _ => []

def Shape.getNext : Shape → List Label
  | .simple _ (.some next)  => getLabels next
  | .loop _ (.some next)    => getLabels next
  | .multi _ _ (.some next) => getLabels next
  | .simple _ .none         => []
  | .loop _ .none           => []
  | .multi _ _ .none        => []
  | .illegal _              => []

def Shape.getAllLabels : Shape → List Label
  | .simple lbl (.some next)        => lbl :: getAllLabels next
  | .simple lbl .none               => lbl :: []
  | .loop (.some body) (.some next) => getAllLabels body ++ getAllLabels next
  | .loop .none        (.some next) => getAllLabels next
  | .loop (.some body) .none        => getAllLabels body
  | .multi l r n                    =>
       (match l with | .none => [] | .some b => getAllLabels b)
    ++ (match r with | .none => [] | .some b => getAllLabels b)
    ++ (match n with | .none => [] | .some b => getAllLabels b)
  | _ => []

partial def Shape.toString : Shape → String
  | .simple l s =>
    let r := opt_toString s
    s!"Simple\n  <{l}>\n  {r}"
  | .loop s₁ s₂ =>
    let r₁ := opt_toString s₁
    let r₂ := opt_toString s₂
    s!"Loop\n  {r₁}\n  {r₂}\n"
  | .multi s₁ s₂ n =>
    let r₁ := opt_toString s₁
    let r₂ := opt_toString s₂
    let r  := opt_toString n
    s!"Multi\n  {r₁}\n  {r₂}\n  {r}\n"
  | .illegal ls => s!"ILLEGAL {ls}\n"
where opt_toString : Option Shape → String
  | .some s => toString s |>.replace "\n" "\n  "
  | .none   => "-"
instance : ToString Shape := ⟨Shape.toString⟩
instance : ToString (Option Shape) where
  toString := fun | .none => "-" | .some s => s.toString

/- This is the primary implement of the Relooper algorithm. There are certainly
   inefficiencies in this implementation but it is *good enough* for now
 -/
mutual
partial def reloop'
    (fuel : Nat)
    (cfg : C0_CFG α β)
    (entries : List Label)
    (labels : List Label)
    : Option Shape :=
  let reach := -- calculate for each entry what we can reach
    labels.map (fun l => (l,
        find_reachable_skipping cfg.digraph l (· ∉ labels)
        |>.fst |>.map (·.node)
      )
    )
  simple fuel cfg entries reach

private partial def simple
    (fuel : Nat)
    (cfg : C0_CFG α β)
    (entries : List Label)
    (reach : List (Label × List Label))
    : Option Shape :=
  if fuel = 0 then .some (.illegal []) else
  match entries with
  | [] => .none
  | l :: [] =>
    -- if you have a single entry and cannot return to it, then you have a
    -- simple block!
    if reach.find? (l = ·.fst) |>.bind (·.snd.find? (· = l)) |>.isNone then
      let entries' := succ cfg.digraph l |>.inter (reach.map (·.fst))
      let reach' :=
        reach.filterMap (fun (l', _) => if l' ≠ l then some l' else none)
      .some (.simple l (reloop' (fuel - 1) cfg entries' reach'))
    else complex (fuel - 1) cfg entries reach
  | _ => complex (fuel - 1) cfg entries reach


private partial def complex
    (fuel : Nat)
    (cfg : C0_CFG α β)
    (entries : List Label)
    (reach : List (Label × List Label))
    : Option Shape :=
  -- if all entries are reachable then create a loop block
  if entries.all (fun l =>
    reach.find? (fun (l', rs) => l = l' && rs.elem l) |>.isSome)
  then -- can return to all entries
    match entries with
    | [] => .none
    | l :: _ => mk_loop entries reach l
  else
    match entries with
    | [] => .none
    | l :: [] => mk_loop entries reach l -- branch needs more than one block
    | l₁ :: l₂ :: ls =>
      /- Try creating a multi block. In C0 this can at most be two so we take
         two entries and try to find all labels that can be reached by one but
         not the other (and vice-versa). -/
      let independ_opt : Option (List Label × List Label) :=
        match reach.find? (·.fst = l₁), reach.find? (·.fst = l₂) with
        | .some (_, rs₁), .some (_, rs₂) =>
          .some (rs₁.diff rs₂, rs₂.diff rs₁)
        | .some (_, rs₁), .none => .some (rs₁, [])
        | .none, .some (_, rs₂) => .some ([], rs₂)
        | .none, .none => .none
      match independ_opt with
      | .some (r₁, r₂) =>
        /- We did find unreachable labels! The handled blocks (blocks that we
           are branching to) are these labels that cannot be reached from one
           another (they are entries). -/
        let handle := fun l rs =>
            reloop' fuel cfg [l] (reach.filterMap (fun (l', _) =>
              if rs.elem l' then .some l' else .none
            )
          )
        let res₁ := handle l₁ r₁
        let res₂ := handle l₂ r₂

        let handled_labels :=
          (res₁.map Shape.getAllLabels |>.getD []).union
          (res₂.map Shape.getAllLabels |>.getD [])
        let valid_succs := reach.map (·.fst) |>.diff handled_labels
        /- The next block is all the labels we could reach from both. The
           entries are the blocks that have an edge from the handled blocks -/
        let next_e :=
          handled_labels
          |>.bind (succ cfg.digraph · |>.inter valid_succs)
          |>.eraseDups
          |>.union (ls.diff handled_labels)
        let next_r := reach.filterMap (fun (l, _) => -- is this correct?
            if ¬r₁.elem l && ¬r₂.elem l then .some l else .none
          )
        .some (.multi res₁ res₂ (reloop' fuel cfg next_e next_r))
      | .none => .some (.illegal entries)
        /- In theory we should try and loop this but since C0 should have
           structured controlflow, we should never reach this case so it is
           more useful to error out here for debugging purposes. -/
          -- mk_loop entries reach l₁
where mk_loop (entries : List Label)
              (reach : List (Label × List Label))
              (l : Label)
              : Option Shape :=
  let inner := reach.filterMap (fun (l', rs) =>
      if l = l' then .none else
      if rs.elem l then .some (l', rs.filter (· ≠ l)) else .none
    ) -- can reach `l`
  let next  := reach.filter (¬ ·.snd.elem l)
  let inner_lbls := inner.map (·.fst)
  let inner_entry := l :: entries.filter (inner_lbls.elem ·)
  let next_entry := (l::inner_lbls).bind (succ cfg.digraph)
    |>.filter (· ∉ l::inner_lbls)
  let inner_shape := reloop' fuel cfg inner_entry inner_lbls
  let next_shape  := reloop' fuel cfg (next_entry) (next |>.map (·.fst))
  .some (.loop inner_shape next_shape)

end

def reloop (cfg : C0_CFG α β) : Option Shape :=
  let vertices := toVertices cfg.digraph
  reloop' (vertices.length * 2) cfg [cfg.start.val] vertices

/-
namespace Test

def l : Nat → Label := fun n => ⟨n, .none⟩

def test1_cfg : C0_CFG Nat Nat :=
  { toCFG :=
    { digraph :=
        (ControlFlow.Digraph.empty : FuncGraphType Label)
        |>.add_edge ⟨l 6, l 8⟩
        |>.add_edge ⟨l 6, l 7⟩
        |>.add_edge ⟨l 7, l 8⟩
        |>.add_edge ⟨l 7, l 7⟩
    , start := ⟨l 6, sorry⟩
    , reachable := sorry
    }
  , name := ⟨0, .some "main"⟩
  , blocks := Std.HashMap.empty
  }

def test2_cfg : C0_CFG Nat Nat :=
  { toCFG :=
    { digraph :=
        (ControlFlow.Digraph.empty : FuncGraphType Label)
        |>.add_edge ⟨l 6, l 7⟩
        |>.add_edge ⟨l 6, l 8⟩
        |>.add_edge ⟨l 7, l 8⟩
        |>.add_edge ⟨l 7, l 7⟩
    , start := ⟨l 6, sorry⟩
    , reachable := sorry
    }
  , name := ⟨0, .some "main"⟩
  , blocks := Std.HashMap.empty
  }

def test3_cfg : C0_CFG Nat Nat :=
  { toCFG :=
    { digraph :=
        (ControlFlow.Digraph.empty : FuncGraphType Label)
        |>.add_edge ⟨l 8, l 9⟩
        |>.add_edge ⟨l 8, l 10⟩
        |>.add_edge ⟨l 12, l 13⟩
        |>.add_edge ⟨l 9, l 11⟩
        |>.add_edge ⟨l 9, l 12⟩
        |>.add_edge ⟨l 13, l 9⟩
        |>.add_edge ⟨l 13, l 10⟩
        |>.add_edge ⟨l 14, l 13⟩
    , start := ⟨l 8, sorry⟩
    , reachable := sorry
    }
  , name := ⟨0, .some "main"⟩
  , blocks := Std.HashMap.empty
  }

#eval test1_cfg
#eval test2_cfg
#eval Id.run IO.println (reloop test1_cfg)
#eval Id.run IO.println (reloop test2_cfg)
#eval Id.run IO.println (reloop test3_cfg)
#eval (reloop test1_cfg).map Shape.getLabels
#eval (.multi (.some <| .simple (l 0) .none)
              (.some <| .simple (l 1) .none)
              (.some <| .simple (l 2) .none)) |> Shape.getLabels
#eval (.loop (.some <| .simple (l 0) .none)
             (.some <| .simple (l 1) .none)) |> Shape.getLabels

end Test
-/
