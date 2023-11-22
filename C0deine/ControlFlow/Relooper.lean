/-
  We use the "Relooper Algorithm" to reconstruct more structured control-flow
  from our less structured basic blocks. While it might be simpler to go from
  a language that represent's C0 control-flow better (like the TST), this would
  make it hard to do many optimisations and run other checks that C0 requires.

  In theory, the code generated via this algorithm shouldn't be too inefficient
  since C0 doesn't have strange control-flow (like goto).

  https://github.com/emscripten-core/emscripten/blob/main/docs/paper.pdf
-/

import C0deine.Context.Label
import C0deine.ControlFlow.CFG
import ControlFlow.FindPath

namespace C0deine.ControlFlow.Relooper

open ControlFlow
open ControlFlow.Digraph
open ControlFlow.Path.Find

/- `simple` represents block with only one exit
 - `loop` represents a block body and the block after the loop
 - `multi` represents branching and then the block after they merge -/
inductive Shape where
| simple : Label → Option Shape → Shape
| loop   : (inner next : Option Shape) → Shape
| multi  : (left right next : Option Shape) → Shape
| illegal : List Label → Shape

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

mutual
partial def reloop'
    (fuel : Nat)
    (cfg : C0_CFG α β)
    (entries : List Label)
    (labels : List Label)
    : Option Shape :=
  let reach :=
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
  if entries.all (fun l =>
    reach.find? (fun (l', rs) => l = l' && rs.elem l) |>.isSome)
  then -- can return to all entries
    match entries with
    | [] => .none
    | l :: _ => mk_loop entries reach l
  else
    match entries with
    | [] => .none
    | l :: [] => mk_loop entries reach l
    | l₁ :: l₂ :: ls =>
      let independ_opt : Option (List Label × List Label) :=
        match reach.find? (·.fst = l₁), reach.find? (·.fst = l₂) with
        | .some (_, rs₁), .some (_, rs₂) =>
          .some (rs₁.diff rs₂, rs₂.diff rs₁)
        | .some (_, rs₁), .none => .some (rs₁, [])
        | .none, .some (_, rs₂) => .some ([], rs₂)
        | .none, .none => .none
      match independ_opt with
      | .some (r₁, r₂) =>
        let handle := fun l rs =>
            reloop' fuel cfg [l] (reach.filterMap (fun (l', _) =>
              if rs.elem l' then .some l' else .none
            )
          )
        let handled_labels := (l₁ :: r₁).union (l₂ :: r₁)
        let valid_succs := reach.map (·.fst) |>.diff handled_labels
        let next_e :=
          handled_labels
          |>.bind (succ cfg.digraph · |>.inter valid_succs)
          |>.eraseDups
          |>.union ls
        let next_r := reach.filterMap (fun (l, _) =>
            if ¬r₁.elem l && ¬r₂.elem l then .some l else .none
          )
        .some (.multi (handle l₁ r₁) (handle l₂ r₂) (reloop' fuel cfg next_e next_r))
      | .none =>
          .some (.illegal entries)
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
  let next_entry := next.filter (fun (n, _) => inner.all (·.snd.elem n))
  let inner_shape := reloop' fuel cfg inner_entry inner_lbls
  let next_shape  := reloop' fuel cfg (next_entry.map (·.fst)) (next |>.map (·.fst))
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

#eval test1_cfg
#eval test2_cfg
#eval Id.run IO.println (reloop test1_cfg)
#eval Id.run IO.println (reloop test2_cfg)
#eval (reloop test1_cfg).map Shape.getLabels
#eval (.multi (.some <| .simple (l 0) .none)
              (.some <| .simple (l 1) .none)
              (.some <| .simple (l 2) .none)) |> Shape.getLabels
#eval (.loop (.some <| .simple (l 0) .none)
             (.some <| .simple (l 1) .none)) |> Shape.getLabels

end Test
-/
