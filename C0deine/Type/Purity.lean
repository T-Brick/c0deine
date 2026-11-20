import C0deine.Type.Tst

namespace C0deine.Type.Purity

abbrev TyVar := Nat

inductive Tag
| atom      -- data that doesn't make sense to have read/write (e.g. ints)
| readonly  -- readonly data
| mutable   -- read/write data
| unknown : TyVar → Tag -- tyvar to be resolved later
deriving DecidableEq, Hashable

def Tag.toString : Tag → String
  | .atom => "atom"
  | .readonly => "readonly"
  | .mutable => "mutable"
  | .unknown x => s!"unknown {x}"
instance : ToString Tag where toString := Tag.toString

inductive Constraint
| eq : Tag → Tag → Constraint
| max : Tag → Tag → Tag → Constraint -- the first is the most restrictive

def Constraint.contradiction : Constraint → Bool
  | .eq .readonly .mutable => true
  | .eq .mutable .readonly => true
  | _ => false -- todo: am i missing some?

/- Replaces t₁ with t₂ in the constraint -/
def Constraint.rewrite (t₁ t₂ : Tag) : Constraint → Constraint
  | .eq ct₁ ct₂ =>
    let ct₁' := if ct₁ == t₁ then t₂ else ct₁
    let ct₂' := if ct₂ == t₁ then t₂ else ct₂
    .eq ct₁' ct₂'
  | .max ct₁ ct₂ ct₃ =>
    let ct₁' := if ct₁ == t₁ then t₂ else ct₁
    let ct₂' := if ct₂ == t₁ then t₂ else ct₂
    let ct₃' := if ct₃ == t₁ then t₂ else ct₃
    .max ct₁' ct₂' ct₃'

def Constraint.reduce_max : Constraint → Constraint
  | .max t .readonly .readonly => .eq t .readonly
  | .max t .mutable .mutable => .eq t .mutable
  | .max t .readonly .mutable => .eq t .readonly
  | .max t .mutable .readonly => .eq t .readonly
  | .max t₁ .atom t₂ => .eq t₁ t₂
  | .max t₁ t₂ .atom => .eq t₁ t₂
  | c => c

def Constraint.toString : Constraint → String
  | .eq t₁ t₂ => s!"{t₁} = {t₂}"
  | .max t t₁ t₂ => s!"{t} = max({t₁}, {t₂})"
instance : ToString Constraint where toString := Constraint.toString

def VarCtx := Symbol.Map Tag
def VarCtx.empty : VarCtx := Symbol.Map.empty

def PureSet := Symbol.Map Unit
def PureSet.empty : PureSet := Symbol.Map.empty

abbrev Error := String
-- structure Error where
  -- message : String
  -- todo: more

end Purity

structure Purity.State where
  vars : VarCtx
  fresh_ty_var : TyVar
  constraints : List Constraint
  -- functions : PureSet

def Purity := ExceptT Purity.Error (StateM Purity.State)
instance : Monad Purity := show Monad (ExceptT _ _) from inferInstance
instance : MonadStateOf Purity.State Purity where
  get s         := ⟨.ok s, s⟩
  set s _       := ⟨.ok (), s⟩
  modifyGet f s := (f s).map .ok id

namespace Purity

open Tst

def new_unknown : Purity Tag := fun s =>
  (pure (.unknown s.fresh_ty_var), { s with fresh_ty_var := s.fresh_ty_var + 1})

def get_var (x : Symbol) : Purity Tag := do
  let s ← get
  match s.vars.get? x with
  | .some t => return t
  | .none =>
    let t := .unknown s.fresh_ty_var
    let vars := s.vars.insert x t
    let fresh_ty_var := s.fresh_ty_var + 1
    set { s with vars, fresh_ty_var }
    return t

def set_var (x : Symbol) (t : Tag) : Purity Unit := fun s =>
  (pure (), { s with vars := s.vars.insert x t })

def add_constraint (c : Constraint) : Purity Unit := fun s =>
  (pure (), { s with constraints := c :: s.constraints })

def expr_constraints (expr : Expr Δ Γ τ) : Purity Tag := do
  match (dependent := true) expr with
  | .num _ _  => return .atom
  | .char _ _ => return .atom
  | .str _ _  => return .atom
  | .var x _  =>
    if τ.isMem then get_var x else return .atom
  | .true _   => return .atom
  | .false _  => return .atom
  | .null _   => return .mutable
  | .unop_int _ _ _ e => return .atom
  | .unop_bool _ _ _ e => return .atom
  | .binop_int _ _ _ _ _ r
  | .binop_bool _ _ _ _ _ r
  | .binop_eq _ _ _ _ _ _ _
  | .binop_rel_int _ _ _ _ _ _ r
  | .binop_rel_char _ _ _ _ _ _ r => return .atom
  | .ternop (τ₂ := τ) _ _ _ tt ff _ =>
    if τ.isMem then
      let restt ← expr_constraints tt
      let resff ← expr_constraints ff
      let t ← new_unknown
      let _ ← add_constraint (.max t restt resff)
      return t
    return .atom
  | .app _ _ _ _ args  => return .atom -- todo check?
  | .alloc _ => return .mutable
  | .alloc_array _ _ _ => return .mutable
  -- todo verify what dot deref inde result
  | .dot _ _ _ _ _ => return .atom
  | .deref _ _ => return .atom
  | .index _ _ _ _ => return .atom
  | .result _ => return .atom
  | .length _ _ => return .atom

def lvalue_constraints (lval : LValue Δ Γ τ) : Purity Tag := do
  match lval with
  | .var x _ => get_var x
  | .dot _ l _ _ _ => lvalue_constraints l
  | .deref _ l => lvalue_constraints l    -- todo check this
  | .index _ _ l _ => lvalue_constraints l -- todo check this

partial def stmt_constraints (stmt : Stmt Δ Γ ρ) : Purity Unit := do
  match stmt with
  | .decl _ _ body => body.toList.foldlM (fun _ => stmt_constraints) ()
  | .decl_init x e _ _ body =>
    if x.type.isMem then
      let t ← expr_constraints e.val
      set_var x.data t
    body.toList.foldlM (fun _ => stmt_constraints) ()
  | .assign_var (τ₁ := τ) lhs _ rhs _ =>
    if τ.isMem then
      let tx ← lvalue_constraints lhs
      let te ← expr_constraints rhs.val
      let _ ← add_constraint (.eq tx .mutable)
      add_constraint (.eq tx te)
    else return ()
  | .assign lhs _ _ _ =>
    let tx ← lvalue_constraints lhs
    -- let te ← expr_constraints rhs.val
    add_constraint (.eq tx .mutable)
    -- add_constraint (.eq tx te)
  | .asnop _ _ lhs _ rhs =>
    let tl ← lvalue_constraints lhs
    let tr ← expr_constraints rhs.val
    add_constraint (.eq tl tr)
  | .expr _ => return () -- todo check
  | .ite _ _ tt ff =>
    let _ ← tt.toList.foldlM (fun _ => stmt_constraints) ()
    ff.toList.foldlM (fun _ => stmt_constraints) ()
  | .while _ _ _ body => -- check annos??
    body.toList.foldlM (fun _ => stmt_constraints) ()
  | .return_void _ => return ()
  | .return_tau _ _ => return ()
  | .assert _ _ => return () -- check?
  | .error _ _ => return ()
  | .anno _ => return () -- check?

def stmts_constraints (stmts : Stmt.List Δ Γ ρ) : Purity Unit :=
  stmts.toList.foldlM (fun _ => stmt_constraints) ()

partial def solve_contraints : Purity Bool := do
  let s ← get
  let constraints := s.constraints
  work constraints
where work (constraints : List Constraint) : Purity Bool := do
  match constraints with
  | .nil => return true
  | c :: cs =>
    if c.contradiction then return false
    match c with
    | .eq t₁ t₂ => work (cs.map (Constraint.rewrite t₁ t₂))
    | .max _ _ _ => work (cs ++ [c.reduce_max])

def gdecl_check_purity (calls : Calls) (g : GDecl Δ₁ Δ₂) : Except Purity.Error Bool := do
  match (dependent := true) g with
  | .fdef f =>
    let state : Purity.State := {
      vars := Symbol.Map.empty
      fresh_ty_var := 0
      constraints := []
    }
    let must_be_pure := calls.getD f.name false
    let state ← (fun _ => do
      if must_be_pure then
        let (exn, state) := f.params.foldlM (fun _ x =>
          set_var (Typ.Typed.data x) .readonly
        ) () state
        let _ ← exn
        return state
      else return state) ()
    let (exn, state) := stmts_constraints f.body state
    let _ ← exn
    -- dbg_trace s!"function {f.name}"
    let is_pure ← solve_contraints state |>.fst
    if must_be_pure && !is_pure then
      throw s!"Function {f.name} is expected to be pure but isn't."
    return is_pure
  | .fdecl _ => return true
  | .sdef _ => return true

def gdecls_check_purity (calls : Calls) (l : GDecl.List Δ₁ Δ₂) : Except Purity.Error Bool := do
  match (dependent := true) l with
  | .nil => return true
  | .cons gs g =>
    let _ ← gdecls_check_purity calls gs
    gdecl_check_purity calls g
  | .update gs => gdecls_check_purity calls gs

def check_purity (p : Prog) : Except Purity.Error Unit := do
  let _ ← gdecls_check_purity p.pure_funcs p.body
  return
