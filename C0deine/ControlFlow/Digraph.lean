import C0deine.AuxDefs

namespace C0deine.ControlFlow

structure Digraph (α : Type) [BEq α] [Hashable α] where
  edges : Std.HashMap α (List α)
  rev_edges : Std.HashMap α (List α)
deriving Inhabited

namespace Digraph

variable [BEq α] [Hashable α]

@[inline] def empty : Digraph α := ⟨Std.HashMap.empty, Std.HashMap.empty⟩

def succ (g : Digraph α) (u : α) : List α := g.edges.findD u []
def pred (g : Digraph α) (u : α) : List α := g.rev_edges.findD u []

structure Edge (α : Type) where
  start  : α
  finish : α
deriving Inhabited, Repr

instance : Coe (Edge α) (α × α) where coe e := (e.start, e.finish)
instance : Coe (α × α) (Edge α) where coe e := ⟨e.fst, e.snd⟩

def add_edge (g : Digraph α) (e : Edge α) : Digraph α :=
  ⟨ g.edges.insert_multi e.start e.finish
  , g.rev_edges.insert_multi e.finish e.start
  ⟩

def remove_edge (g : Digraph α) (e : Edge α) : Digraph α :=
  ⟨ g.edges.insert e.start (g.succ e.start |>.filter (¬e.finish == ·))
  , g.rev_edges.insert e.finish (g.pred e.finish |>.filter (¬e.start == ·))
  ⟩

def toEdges (g : Digraph α) : List (Edge α) :=
  g.edges.toList |>.bind (fun (u, vs) => vs.map (u, ·))
def ofEdges (edges : List (Edge α)) : Digraph α := edges.foldl add_edge empty

def toVertices (g : Digraph α) : List α := g.edges.toList |>.map (·.fst)
def ofVertices (succ : α → List α) (vs : List α) : Digraph α :=
  vs.bind (fun v => succ v |>.map (v, ·)) |> ofEdges

def reachable (g : Digraph α) (s : α) := explore [] [s] (g.toVertices.length)
where explore (visited : List α) (frontier : List α) (fuel : Nat) : List α :=
  if fuel = 0 then visited else
  match frontier with
  | .nil => visited
  | .cons v vs =>
    let visited'  := v :: visited
    let frontier' := succ g v |>.diff visited' |>.append vs
    explore visited' frontier' (fuel - 1)

end Digraph
