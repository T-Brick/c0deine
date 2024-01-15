/- C0deine - InferenceRule
   Experimental tool for generating nice inference rules from an inductive type
   in Lean.
   - Thea Brick
 -/

import C0deine.Type.Tst

namespace C0deine.Experimental

open Lean Meta Tst

-- temp should move?
scoped notation:50 "int"    => Typ.prim Typ.Primitive.int
scoped notation:50 "char"   => Typ.prim Typ.Primitive.char
scoped notation:50 "string" => Typ.prim Typ.Primitive.string
scoped notation:50 "bool"   => Typ.prim Typ.Primitive.bool

scoped notation:50 "\\length " e:51 => Expr.length e

def getConsType (val : Name) : MetaM Lean.Expr := do
  let env ← getEnv
  match env.find? val with
  | some (.ctorInfo info) => pure info.type
  | _ => panic! s!"No {val} constructor"

-- default name given to language-exprs from the lean-type
def InferenceRule.TyDefault := Name → Option String
instance : Inhabited InferenceRule.TyDefault where
  default :=
    fun | ``Int32      => some "n"
        | ``Char       => some "c"
        | ``String     => some "s"
        | ``Symbol     => some "x"
        | ``BinOp.Int  => some "int_op"
        | ``BinOp.Bool => some "bool_op"
        | ``UnOp       => some "op"
        | ``Comparator => some "op"
        | _            => none

-- based on the lean-type, should this be in the antecedent
abbrev InferenceRule.TyAnte := List Name
instance : Inhabited InferenceRule.TyAnte := ⟨[``Eq, ``Subtype, ``Not]⟩

-- extracts the language-type from the expression rule's lean-type
-- do we need?
def InferenceRule.TyExtractor := Lean.Expr → MetaM (Option (Lean.Expr × String))
def InferenceRule.TyExtractor.default : InferenceRule.TyExtractor
  | .app fn arg => do return some (fn, toString (← ppExpr arg))
  | _ => return none

instance : Inhabited InferenceRule.TyExtractor :=
  ⟨InferenceRule.TyExtractor.default⟩

def InferenceRule.Judgement := String → String
instance : Inhabited InferenceRule.Judgement := ⟨(fun τ => s!" : {τ}")⟩

-- todo monadify
structure InferenceRule.Style where
  contextSyms : List Name   := [`Δ, `Γ] -- can this be automated?
  contextSep  : String      := "; "
  tee         : String      := " ⊢"
  recurTySym  : List Name   := [``Tst.Expr]
  recurObjSym : String      := "e"
  tyDefaults  : TyDefault   := default
  tyExtractor : TyExtractor := default
  tyAnte      : TyAnte      := default
  judgement   : Judgement   := default
instance : Inhabited InferenceRule.Style := ⟨{}⟩

structure InferenceRule where
  antecedents : List String
  consequent  : String
instance : ToString InferenceRule where
  toString rule :=
    let antes := "\n".intercalate rule.antecedents.reverse
    s!"{antes}\n---\n{rule.consequent}"

namespace InferenceRule

-- todo this is a mess
def consumeContext (style : Style) (expr : Lean.Expr)
    : Option String :=
  aux style.contextSyms.reverse expr
where aux : List Name → Lean.Expr → Option String
  | [], _ => some ""
  | sym::[], .fvar ⟨sym'⟩
  | sym::[], .const sym' _ =>
    if sym = sym' then return sym.toString else none
  | sym::[], .app _fn arg => do
    let str₁ ← aux [sym] arg
    return str₁
  | sym::syms, .app fn arg => do
    let str₁ ← aux [sym] arg
    let str₂ ← aux syms fn
    return str₂ ++ style.contextSep ++ str₁
  | _, expr => some s!"invalid {expr.ctorName}"

def checkType
    (style : Style)
    (p : Name → Option α)
    : Lean.Expr → Option α
  | .const declName _ => p declName
  | .app fn _ => checkType style p fn
  | _ => none

structure Builder where
  bindings  : List Name
  expr      : Lean.Expr     -- expression working on
  rule      : InferenceRule
  cur       : String        -- current string to add to rule
  rec_comps : Nat           -- number of recursive components


-- couldn't find an existing function that does this so here
def replaceDeBruijn (bindings : List Name) : Lean.Expr → Lean.Expr
  | .bvar i => .fvar ⟨bindings.get! i⟩
  | .app fn arg =>
    .app (replaceDeBruijn bindings fn) (replaceDeBruijn bindings arg)
  | .lam binderName ty body info =>
    let bindings' := binderName :: bindings
    .lam binderName
      (replaceDeBruijn bindings ty)
      (replaceDeBruijn bindings' body)
      info
  | .forallE binderName ty body info =>
    let bindings' := binderName :: bindings
    .forallE binderName
      (replaceDeBruijn bindings ty)
      (replaceDeBruijn bindings' body)
      info
  | .letE binderName ty value body nonDep =>
    let bindings' := binderName :: bindings
    .letE binderName
      (replaceDeBruijn bindings ty)
      (replaceDeBruijn bindings value) -- is this right?
      (replaceDeBruijn bindings' body)
      nonDep
  | .mdata data expr =>
    .mdata data (replaceDeBruijn bindings expr)
  | .proj typeName index struct =>
    .proj typeName index (replaceDeBruijn bindings struct)
  | expr => expr

def buildJudgement (style : Style) (builder : Builder)
    : MetaM (Option String) := do
  let ty? ← style.tyExtractor (replaceDeBruijn builder.bindings builder.expr)
  return ty?.bind (fun (expr, τ) => do
    let judge := style.judgement τ
    let ctx_str ← consumeContext style expr
    return ctx_str ++ style.tee ++ builder.cur ++ judge
  )

def buildExpr (style : Style) (name : Name) (acc : Builder)
    : Lean.Expr → MetaM (Option Builder)
  | .lam binder ty body _
  | .forallE binder ty body _ => do
    let acc_old := acc
    let acc := { acc with bindings := binder :: acc.bindings
                        , expr := body
                        }
    if let some str := checkType style style.tyDefaults ty then
      let cur := s!"{acc.cur} {str}"
      buildExpr style name {acc with cur} body
    else
      -- todo make this cleaner : )
      let is_rec :=
        checkType style (if · ∈ style.recurTySym then some () else none) ty
      let is_ante :=
        checkType style (if · ∈ style.tyAnte then some () else none) ty
      if is_rec.isSome then
        let e' := s!" {style.recurObjSym}_{acc.rec_comps}"
        let cur  := s!"{acc.cur}{e'}"
        match ← buildJudgement style {acc_old with expr := ty, cur := e'} with
        | some judge =>
          let antecedents := judge :: acc.rule.antecedents
          let rule := { acc.rule with antecedents }
          let acc  := { acc with rule, cur, rec_comps := acc.rec_comps + 1 }
          buildExpr style name acc body
        | none => return none
      else if is_ante.isSome then
        let ty_str := toString <| ← ppExpr (replaceDeBruijn acc_old.bindings ty)
        let str :=
          if binder.isInternal
          then ty_str
          else s!"{toString binder} ∈ {ty_str}"
        let antecedents := str :: acc.rule.antecedents
        let rule := { acc.rule with antecedents }
        buildExpr style name { acc with rule } body
      else
        buildExpr style name acc body
  | expr => do -- reached end of type, i.e. the result
    let acc := { acc with expr }
    if acc.cur = "" then
      let cur :=
        if let str :: _ := name.componentsRev
        then " " ++ toString str
        else " ?"
      return some { acc with cur }
    else return some acc

def build
    (style : Style := default)
    (name : Name)
    (expr : Lean.Expr)
    : MetaM (Option InferenceRule) := do
  -- let (ctx_str, expr) ← consumeContext style expr

  let builder_init := ⟨style.contextSyms.reverse, expr, ⟨[], ""⟩, "", 0⟩
  let builder? ← buildExpr style name builder_init expr

  if let some builder := builder? then
    let judge? ← buildJudgement style builder
    match judge? with
    | some judge =>
      return InferenceRule.mk builder.rule.antecedents judge
    | none =>
      return InferenceRule.mk builder.rule.antecedents "judge :("
  else return none

#eval
  Elab.Command.runTermElabM fun _ => do
    let name := ``Expr.binop_int
    let x ← getConsType name
    let rule? ← InferenceRule.build default name x
    match rule? with
    | some rule =>
      IO.println s!"{rule}"
      IO.println s!"\n\n{x}\n"
    | none =>
      IO.println s!"{x}\n"
      IO.println "Could not build rule :(\n"
      IO.println s!"{← ppExpr x}\n"
