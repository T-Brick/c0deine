import C0deine.AuxDefs

namespace C0deine.ControlFlow

structure Digraph (α : Type) [BEq α] [Hashable α] where
  edges     : Std.HashMap α (List α)
  rev_edges : Std.HashMap α (List α)
deriving Inhabited

namespace Digraph

variable [DecidableEq α] [Hashable α]

@[inline] def empty : Digraph α := ⟨Std.HashMap.empty, Std.HashMap.empty⟩

def succ (g : Digraph α) (v : α) : List α := g.edges.findD v []
def pred (g : Digraph α) (v : α) : List α := g.rev_edges.findD v []

structure Edge (α : Type) where
  start  : α
  finish : α
deriving Inhabited, Repr, DecidableEq

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

def add_vertex (g : Digraph α) (v : α) : Digraph α :=
  ⟨ g.edges.insert v [], g.rev_edges ⟩
def remove_vertex (g : Digraph α) (v : α) : Digraph α :=
  ⟨ g.edges.mapVal (fun _ us => us.filter (¬v == ·)) |>.erase v
  , g.rev_edges.mapVal (fun _ us => us.filter (¬v == ·)) |>.erase v
  ⟩

def toEdges (g : Digraph α) : List (Edge α) :=
  g.edges.toList |>.bind (fun (u, vs) => vs.map (u, ·))
def ofEdges (edges : List (Edge α)) : Digraph α := edges.foldl add_edge empty

def toVertices (g : Digraph α) : List α :=
  g.edges.toList |>.bind (fun (u, v) => u :: v) |>.eraseDups
def ofVertices (succ : α → List α) (vs : List α) : Digraph α :=
  vs.bind (fun v => succ v |>.map (v, ·)) |> ofEdges

def has_edge (e : Edge α) (g : Digraph α) : Prop := e ∈ g.toEdges
def has_vertex (v : α) (g : Digraph α) : Prop := g.edges.contains v

def elem_edge (e : Edge α) (g : Digraph α) : Bool := g.toEdges.elem e
def elem_vertex (v : α) (g : Digraph α) : Bool := g.edges.contains v


instance : Membership (Edge α) (Digraph α) := ⟨has_edge⟩
instance : Membership α (Digraph α) := ⟨has_vertex⟩

-- todo change to something more provable?
-- mask limits which nodes we can visit (i.e. they must be in the mask)
def reachable_mask (g : Digraph α) (s : α) (mask : List α) :=
  explore [] (succ g s) (g.toVertices.length * 1000)
where explore (visited : List α) (frontier : List α) (fuel : Nat) : List α :=
  if fuel = 0 then visited else
  match frontier with
  | .nil => visited
  | .cons v vs =>
    let visited'  := v :: visited
    let frontier' :=
      visited'.bind (succ g) ++ vs
      |>.eraseDups
      |>.diff visited'
      |>.inter mask
    explore visited' frontier' (fuel - 1)

def reachable (g : Digraph α) (s : α) :=
  reachable_mask g s g.toVertices

end Digraph
