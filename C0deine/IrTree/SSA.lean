import C0deine.IrTree.IrTree
import C0deine.IrTree.Rewriter
import C0deine.Type.Typ

namespace C0deine.IrTree.SSA

open Typ

/- Mapping of Temp to Labels that define it -/
abbrev Definitions := Std.HashMap Temp (Std.HashSet Label)
abbrev Usage := Std.HashMap Nat Nat
-- todo move this to ControlFlow lib?
abbrev Dom.Frontier := Label → Std.HashSet Label
abbrev Dom.Tree := Std.HashMap Label (Std.HashSet Label)

namespace Definitions

def update (lbl : Label) (defs : Definitions) (temp : Temp) : Definitions :=
  let def_set := defs.getD temp {}
  let new_def_set := def_set.insert lbl
  defs.insert temp new_def_set

def stmt (lbl : Label) (defs : Definitions) : Stmt → Definitions
  | .move dest _ => update lbl defs dest.data
  | .effect dest _ _ _ => update lbl defs dest.data
  | .call dest _ _ => update lbl defs dest.data.data
  | .alloc dest _ => update lbl defs dest
  | .load dest _ => update lbl defs dest.data
  | .store _ _ => defs
  | .copy _ _ _ => defs
  | .check _ => defs
  | .phi dest _ => update lbl defs dest

def block (defs : Definitions) (lbl : Label) : Block → Definitions :=
  (·.body.foldl (stmt lbl) defs)

def func (f : Func) : Definitions :=
  f.blocks.fold block Std.HashMap.emptyWithCapacity

end Definitions

namespace Phi

structure Context where
  defs : Definitions
  frontier : Dom.Frontier
  phi_add_list : Std.HashMap Label (Std.HashSet Temp)
  visited : Std.HashSet Label
  worklist : List Label

def start_new_var (t : Temp) : StateM Context Unit := fun s =>
  let worklist := s.defs.getD t {} |>.toList
  ((), { s with worklist, visited := {} })

@[inline] def get_frontier (l : Label) : StateM Context (Std.HashSet Label) :=
  fun s => (s.frontier l, s)

@[inline] def add_visited (l : Label) : StateM Context Unit :=
  fun s => ((), { s with visited := s.visited.insert l })
@[inline] def already_visited (l : Label) : StateM Context Bool :=
  fun s => (s.visited.contains l, s)

@[inline] def add_worklist (l : Label) : StateM Context Unit := do
  if ← already_visited l then
    fun s => ((), { s with worklist := l :: s.worklist})
@[inline] def next : StateM Context (Option Label) := fun s =>
  match s.worklist with
  | .nil => (.none, s)
  | .cons l ls => (.some l, { s with worklist := ls })

def add_phi_to_list (t : Temp) (l : Label) : StateM Context Unit := fun s =>
  let add_vars := s.phi_add_list.getD l {} |>.insert t
  let phi_add_list := s.phi_add_list.insert l add_vars
  let def_labels := s.defs.getD t {} |>.insert l
  let defs := s.defs.insert t def_labels
  return ((), { s with defs, phi_add_list })

def add_var_phi_nodes (fuel : Nat) (t : Temp) : StateM Context Unit := do
  let _ ← start_new_var t
  work fuel
where work (fuel : Nat) : StateM Context Unit := do
  if fuel = 0 then return
  match ← next with
  | .none => return
  | .some d =>
  let blocks ← get_frontier d
  let _ ← blocks.foldM (fun _ => add_phi_to_list t) ()
  work (fuel - 1)

def insert_phi_nodes (f : Func) (ctx : Context) : Func :=
  let add_list := ctx.phi_add_list
  let blocks := f.blocks.map (fun l b =>
    let temps := add_list.getD l {} |>.toList |>.map (fun t => .phi t [])
    let body := temps ++ b.body
    { b with body }
  )
  { f with blocks }

def add_nodes (f : Func) (frontier : Dom.Frontier) : Func :=
  let defs := Definitions.func f
  let ctx : Context := {
    defs,
    frontier,
    phi_add_list := Std.HashMap.emptyWithCapacity
    visited := {}
    worklist := []
  }
  let size := f.blocks.size
  let ctx := defs.keys.mapM (add_var_phi_nodes size) ctx |>.snd
  insert_phi_nodes f ctx

def add_arg (f : Func) (usage : Usage) : Label → Func :=
  f.rewrite_stmt_at (fun
    | .phi dest args =>
      match usage.get? dest.id with
      | .none => .some (.phi dest args)
      | .some usage_id =>
        .some (.phi dest ({ dest with ssa_number := .some usage_id} :: args))
    | s => .some s
  )

end Phi

namespace Rename

structure Context where
  frontier : Dom.Frontier
  dom_tree : Dom.Tree
  -- for getting a fresh number
  defs_map : Std.HashMap Nat Nat
  -- for getting the current usage id for the specific scope
  usage_map : Usage

def fresh_temp (temp : Temp) : StateM Context Temp := do
  let ctx ← get
  let ssa_id := (ctx.defs_map.getD temp.id 0) + 1
  set ({
    frontier := ctx.frontier
    dom_tree := ctx.dom_tree
    defs_map := ctx.defs_map.insert temp.id ssa_id,
    usage_map := ctx.usage_map.insert temp.id ssa_id
  } : Context)
  return { temp with ssa_number := .some ssa_id }

def fresh_sized_temp (t : SizedTemp) : StateM Context SizedTemp := do
  return ⟨t.size, ← fresh_temp t.temp⟩

def temp (temp : Temp) : StateM Context Temp := do
  let ctx ← get
  let ssa_id := ctx.usage_map.getD temp.id 0
  return { temp with ssa_number := .some ssa_id }

def sized_temp (t : SizedTemp) : StateM Context SizedTemp := do
  return ⟨t.size, ← temp t.temp⟩

def expr : Expr → StateM Context Expr :=
  ExprRewriter.rewriteM_expr? (fun
    | .temp t => return .some <| .temp (← sized_temp t)
    | _ => return .none
  )

def stmt (s : Stmt) : StateM Context Stmt := do
  let s ← ExprRewriter.rewriteM_expr expr s
  match s with
  | .move dest e =>
    let dest ← fresh_sized_temp dest
    return .move dest e
  | .effect dest op l r =>
    let dest ← fresh_sized_temp dest
    return .effect dest op l r
  | .call dest name args =>
    let dest := Typed.mk dest.type (← fresh_sized_temp dest.data)
    return .call dest name args
  | .alloc dest size =>
    let dest ← fresh_temp dest
    return .alloc dest size
  | .load dest addr =>
    let dest ← fresh_sized_temp dest
    return .load dest addr
  | .store addr src => return .store addr src
  | .copy dest src len => return .copy dest src len
  | .check c => return .check c
  | .phi dest args =>
    let dest ← fresh_temp dest
    -- let args ← args.mapM sized_temp
    return .phi dest args

def blockexit (exit : BlockExit) : StateM Context BlockExit := do
  match exit with
  | .jump lbl => return .jump lbl
  | .cjump t hotpath tt ll => return .cjump (← temp t) hotpath tt ll
  | .return e? => return .return (← ExprRewriter.rewriteM_expr expr e?)
  | .error e => return .error (← ExprRewriter.rewriteM_expr expr e)

def block (f : Func) (b : Block) : StateM Context Func := do
  let b ← StmtRewriter.rewriteM_stmt (fun s => do return ← stmt s) b
  let exit ← blockexit b.exit
  return{ f with blocks := f.blocks.insert b.label { b with exit } }

end Rename

namespace Convert

partial def block (f : Func) (b : Block) : StateM Rename.Context Func := do
  -- rename all the temps
  let f ← Rename.block f b

  -- add φ-nodes to all successors
  let succ := b.succ_labels
  let ctx ← get
  let f := succ.foldl (fun f => Phi.add_arg f ctx.usage_map) f

  -- recurse on the children in the dominator tree
  return ← ctx.dom_tree.getD b.label {} |>.toList |>.foldlM (fun f l => do
    let f ← block f (f.blocks.get! l)
    -- don't want to preserve all changes to the children context between them
    let child_ctx ← get
    set { ctx with defs_map := child_ctx.defs_map }
    return f
  ) f

open _root_.ControlFlow in
def func (f : Func) : Option Func := do
  let dom_res ← Dom.Algorithm.compute f.toCFG
  let idom := Dom.Algorithm.get_immediate_dominator dom_res
  let frontier ← Dom.Algorithm.get_dominance_frontier f.toCFG idom

  let block_labels := f.blocks.keys
  let dom_tree : Dom.Tree := block_labels.foldl (fun tree l₁ =>
    match idom l₁ with
    | .none => tree
    | .some l₂ => tree.insert l₂ (tree.getD l₂ {} |>.insert l₁)
  ) {}

  -- first add the phi functions
  let f := Phi.add_nodes f frontier

  -- then rename the variables
  let ctx : Rename.Context := {
    frontier,
    dom_tree,
    defs_map := Std.HashMap.emptyWithCapacity
    usage_map := Std.HashMap.emptyWithCapacity
  }

  let ⟨args, ctx⟩ := f.args.mapM (Rename.fresh_sized_temp) ctx
  return Convert.block { f with args } f.entry_block ctx |>.fst

end Convert

def convert (p : Prog) : Prog :=
  { p with funcs := p.funcs.filterMap Convert.func }
