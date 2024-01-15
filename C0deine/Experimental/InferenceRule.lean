/- C0deine - InferenceRule
   Experimental tool for generating nice inference rules from an inductive type
   in Lean.
   TODO: clean up this file
   - Thea Brick
 -/

import C0deine.Type.Tst

namespace C0deine.Experimental

open Lean Meta Tst

def getConsType (val : Name) : MetaM Lean.Expr := do
  let env ← getEnv
  match env.find? val with
  | some (.ctorInfo info) => pure info.type
  | _ => panic! s!"No {val} constructor"

private def _root_.Lean.Name.lastToString (val : Name) : String :=
  if let str :: _ := val.componentsRev
  then toString str
  else "?"

-- default name given to language-exprs from the lean-type
def InferenceRule.TyDefault := Name → Name → Option String
instance : Inhabited InferenceRule.TyDefault where
  default :=
    fun | _, ``Int32      => some "n"
        | _, ``Char       => some "c"
        | _, ``String     => some "s"
        | n, ``Symbol     => some n.toString
        | _, ``BinOp.Int  => some "int_op"
        | _, ``BinOp.Bool => some "bool_op"
        | _, ``UnOp       => some "op"
        | _, ``Comparator => some "op"
        | _, _            => none

-- based on the lean-type, should this be in the antecedent
abbrev InferenceRule.TyAnte := List Name
instance : Inhabited InferenceRule.TyAnte :=
  ⟨[``Eq, ``Subtype, ``Not]⟩

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

-- this makes the rules prettier/more like what'd one would expect
def InferenceRule.MkJudgeObj := Option Name → List String → String
instance : Inhabited InferenceRule.MkJudgeObj where
  default :=
    fun | some ``Expr.ternop, [c, t, f]   => s!"({c} ? {t} : {f})"
        | some ``Expr.alloc, ids          => " ".intercalate ids ++ "(τ)"
        | some ``Expr.alloc_array, [e]    => s!"alloc_array(τ, {e})"
        | some ``LValue.dot, [_s, e, field]
        | some ``Expr.dot, [_s, e, field] => s!"{e}.{field}"
        | some ``LValue.deref, ids
        | some ``Expr.deref, ids          => "*" ++ " ".intercalate ids
        | some ``LValue.index, [arr, idx]
        | some ``Expr.index, [arr, idx]   => s!"{arr}[{idx}]"
        | some ``Expr.result, ids         => "\\" ++ " ".intercalate ids
        | some ``Expr.length, ids         => " ".intercalate ("\\length" :: ids)
        | _, ids => " ".intercalate ids

-- todo monadify
structure InferenceRule.Style where
  contextSyms : List Name   := [`Δ, `Γ] -- can this be automated?
  contextSep  : String      := "; "
  tee         : String      := " ⊢"
  recurTySym  : List Name
  recurObjSym : String
  tyDefaults  : TyDefault   := default
  tyExtractor : TyExtractor := default
  tyAnte      : TyAnte      := default
  judgement   : Judgement   := default
  mkJudgeObj  : MkJudgeObj  := default

def InferenceRule.Style.expr : InferenceRule.Style :=
  { recurTySym  := [``Tst.Expr]
  , recurObjSym := "e"
  }

def InferenceRule.Style.lval : InferenceRule.Style :=
  { recurTySym  := [``Tst.LValue, ``Tst.Expr]
  , recurObjSym := "lv"
  }

structure InferenceRule where
  name        : String
  antecedents : List String
  consequent  : String
instance : ToString InferenceRule where
  toString rule :=
    let antes := "\n".intercalate rule.antecedents.reverse
    s!"{antes}\n--- ({rule.name})\n{rule.consequent}"

namespace InferenceRule

private def latexify (str : String) : String :=
  str.replace "Δ" "\\Delta"
  |>.replace "Γ" "\\Gamma"
  |>.replace " " "\\;"
  |>.replace "{" "\\{"
  |>.replace "}" "\\}"
  |>.replace "Typ.intersect" "\\texttt{intersect}"
  |>.replace "GCtx.struct" "\\texttt{GCtx.struct}"
  |>.replace "binop_rel₁" "binop_rel1"
  |>.replace "binop_rel₂" "binop_rel2"
  |>.replace "int" "\\texttt{int}"
  |>.replace "bool" "\\texttt{bool}"
  |>.replace "char" "\\texttt{char}"
  |>.replace "string" "\\texttt{string}"
  |>.replace "any" "\\texttt{any}"
  |>.replace "*" "\\texttt{*}"
  |>.replace "[]" "\\texttt{[]}"
  |>.replace "struct\\;" "\\texttt{struct}"
  |>.replace "alloc" "\\texttt{alloc}"
  |>.replace "_array" "\\texttt{_array}"
  |>.replace "\\result" "\\texttt{\\textbackslash result}"
  |>.replace "\\length" "\\texttt{\\textbackslash length}"
  |>.replace "true" "\\texttt{true}"
  |>.replace "false" "\\texttt{false}"
  |>.replace "null" "\\texttt{null}"
  |>.replace "some" "\\texttt{some}"
  |>.replace "none" "\\texttt{none}"
  |>.replace "_" "\\_"
  |>.replace "τ" "\\tau"
  |>.replace "₁" "_1"
  |>.replace "₂" "_2"
  |>.replace "₃" "_3"
  |>.replace "⊢" "\\vdash "
  |>.replace "∈" "\\in "
  |>.replace "¬" "\\lnot "
  |>.replace "↑" "\\uparrow "
  |>.replace "Status.Symbol.var" "\\texttt{Status.Symbol.var}"
  |>.replace "Typ.equiv" "\\texttt{equiv}"
  |>.replace "UnOp.type" "\\texttt{UnOp.type}"
  |>.replace "Comparator.isEquality" "\\texttt{isEqualityOp}"

def toLaTeX (rule : InferenceRule) : String :=
  let antes_strs := rule.antecedents.map (latexify) |>.reverse
  let antes :=
    if antes_strs = []
    then "\\quad"
    else "  \\\\\n    ".intercalate antes_strs
  let conse := latexify rule.consequent
  let name  := latexify rule.name
  s!"\\inferrule
  \{ {antes}\n  }
  \{ {conse} }
  \\; \\textsc\{{name}}"

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
  | _, _ => none

def checkType
    (style : Style)
    (p : Name → Option α)
    : Lean.Expr → Option α
  | .const declName _ => p declName
  | .app fn _ => checkType style p fn
  | _ => none

structure Builder where
  name      : Option Name
  bindings  : List Name
  expr      : Lean.Expr     -- expression working on
  rule      : InferenceRule
  cur       : List String   -- current judgement object
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
    let cur := style.mkJudgeObj builder.name builder.cur.reverse
    return s!"{ctx_str}{style.tee} {cur}{judge}"
  )

def buildExpr (style : Style) (name : Name) (acc : Builder)
    : Lean.Expr → MetaM (Option Builder)
  | .lam binder ty body _
  | .forallE binder ty body _ => do
    let acc_old := acc
    let acc := { acc with bindings := binder :: acc.bindings
                        , expr := body
                        }
    if let some str := checkType style (style.tyDefaults binder) ty then
      buildExpr style name {acc with cur := str :: acc.cur} body
    else
      -- todo make this cleaner : )
      let is_rec :=
        checkType style (if · ∈ style.recurTySym then some () else none) ty
      let is_ante :=
        checkType style (if · ∈ style.tyAnte then some () else none) ty
      if is_rec.isSome then
        let e' := s!"{style.recurObjSym}{acc.rec_comps}"
        let ante_acc :=
          { acc_old with expr := ty
                       , cur  := [e']
                       , name := none
          }
        match ← buildJudgement style ante_acc with
        | some judge =>
          let antecedents := judge :: acc.rule.antecedents
          let rule := { acc.rule with antecedents }
          let cur  := e' :: acc.cur
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
    if acc.cur = [] then
      let cur := [name.lastToString]
      return some { acc with cur }
    else return some acc

def build
    (style : Style)
    (name : Name)
    (expr : Lean.Expr)
    : MetaM (Option InferenceRule) := do
  let builder_init :=
    { name
    , bindings  := style.contextSyms.reverse
    , expr
    , rule      := ⟨name.lastToString, [], ""⟩
    , cur       := []
    , rec_comps := 0
    }
  match ← buildExpr style name builder_init expr with
  | some builder =>
    let judge? ← buildJudgement style builder
    match judge? with
    | some judge =>
      return InferenceRule.mk builder.rule.name builder.rule.antecedents judge
    | none =>
      return none
  | none => return none

private def exprs := -- could be autogenerated once `app` is fixed
  [ ``Expr.num
  , ``Expr.char
  , ``Expr.str
  , ``Expr.var
  , ``Expr.true
  , ``Expr.false
  , ``Expr.null
  , ``Expr.unop
  , ``Expr.binop_int
  , ``Expr.binop_bool
  , ``Expr.binop_eq
  , ``Expr.binop_rel₁
  , ``Expr.binop_rel₂
  , ``Expr.ternop
  -- , ``Tst.Expr.app
  , ``Expr.alloc
  , ``Expr.alloc_array
  , ``Expr.dot
  , ``Expr.deref
  , ``Expr.index
  , ``Expr.result
  , ``Expr.length
  ]

private def lvals :=
  [ ``LValue.var
  , ``LValue.dot
  , ``LValue.deref
  , ``LValue.index
  ]

open Typ.Notation

private def printLaTeX (style : InferenceRule.Style) (names : List Name) := do
  names.mapM (fun name => do
    let x ← getConsType name
    let rule? ← InferenceRule.build style name x
    match rule? with
    | some rule =>
      IO.println s!"{rule.toLaTeX}\n\n\\\\\n"
    | none => IO.println "Could not build rule {name.toString} :(\n"
  )

-- todo: currently '``Tst.Expr.app' doesn't work because of the ∀'s
#eval
  Elab.Command.runTermElabM fun _ => do
    let name := ``Tst.Expr.length
    let x ← getConsType name
    let rule? ← InferenceRule.build .expr name x
    match rule? with
    | some rule =>
      IO.println s!"{rule}"
      IO.println s!"\n\n{rule.toLaTeX}"
      IO.println s!"\n\n{x}\n\n{← ppExpr x}"
    | none =>
      IO.println s!"{x}\n"
      IO.println "Could not build rule {name.toString} :(\n"
      IO.println s!"{← ppExpr x}\n"

-- need to run thru elab to get nice type notation
#eval
  Elab.Command.runTermElabM fun _ => do
    printLaTeX .expr exprs

#eval
  Elab.Command.runTermElabM fun _ => do
    printLaTeX .lval lvals
