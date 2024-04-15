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

def getIndConsNames (val : Name) : MetaM (List Name) := do
  let env ← getEnv
  match env.find? val with
  | some (.inductInfo info) =>
    pure info.ctors
  | _ => panic! s!"No {val} inductive"

def getIndConsTypes (val : Name) : MetaM (List Lean.Expr) := do
  let env ← getEnv
  match env.find? val with
  | some (.inductInfo info) =>
    pure (← info.ctors.mapM getConsType)
  | _ => panic! s!"No {val} inductive"

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

-- extracts the judgement "result" from the expression rule's lean-type
def InferenceRule.ResExtractor := Lean.Expr → MetaM (Option (Lean.Expr × String))
def InferenceRule.ResExtractor.default : InferenceRule.ResExtractor
  | .app fn arg => do return some (fn, toString (← ppExpr arg))
  | _ => return none

instance : Inhabited InferenceRule.ResExtractor :=
  ⟨InferenceRule.ResExtractor.default⟩

def InferenceRule.Conclusion := String → String → String
instance : Inhabited InferenceRule.Conclusion := ⟨(fun e τ => s!"{e} : {τ}")⟩

-- this makes the rules prettier/more like what'd one would expect
def InferenceRule.MkJudgeObj := Option Name → List String → String
instance : Inhabited InferenceRule.MkJudgeObj where
  default :=
    fun | some ``Expr.ternop, [c, t, f]   => s!"({c} ? {t} : {f})"
        | some ``Expr.alloc, ids          => " ".intercalate ids ++ "(τ)"
        | some ``Expr.alloc_array, [e]    => s!"alloc_array(τ, {e})"
        | some ``LValue.dot, [_s, _,  e, field]
        | some ``Expr.dot, [_s, _, e, field] => s!"{e}.{field}"
        | some ``LValue.deref, ids
        | some ``Expr.deref, ids          => "*" ++ " ".intercalate ids
        | some ``LValue.index, [arr, idx]
        | some ``Expr.index, [arr, idx]   => s!"{arr}[{idx}]"
        | some ``Expr.result, ids         => "\\" ++ " ".intercalate ids
        | some ``Expr.length, ids         => " ".intercalate ("\\length" :: ids)
        | some ``Anno.requires, [e]       => s!"//@requires {e};"
        | some ``Anno.ensures, [e]        => s!"//@ensures {e};"
        | some ``Anno.loop_invar, [e]     => s!"//@loop_invariant {e};"
        | some ``Anno.assert, [e]         => s!"//@assert {e};"
        | some ``Stmt.decl, [x, b]         => s!"decl({x}, {b});"
        | some ``Stmt.decl_init, [x, e, b] => s!"decl_init({x}, {e}, {b});"
        | some ``Stmt.assign_var, [l, e]   => s!"{l} = {e};"
        | some ``Stmt.assign, [l, e]       => s!"{l} = {e};"
        | some ``Stmt.asnop, [l, op, e]    => s!"{l} {op}= {e};"
        | some ``Stmt.expr, [e]            => s!"{e};"
        | some ``Stmt.ite, [c, t, f]       => s!"if({c}, {t}, {f});"
        | some ``Stmt.while, [c, b]        => s!"while({c}, {b});"
        | some ``Stmt.return_tau, [e]      => s!"return {e};"
        | some ``Stmt.assert, [e]          => s!"assert({e});"
        | some ``Stmt.error, [e]           => s!"error({e});"
        | some ``Stmt.List.nil, _          => "nop;"
        | some ``Stmt.List.cons, [s, b]    => s!"seq({s}, {b});"
        | _, ids => " ".intercalate ids


structure InferenceRule.Judgement where
  contextSyms  : List Name    := [`Δ, `Γ] -- should be automatable
  contextSep   : String       := "; "
  tee          : String       := " ⊢ "
  recurTySym   : List Name                -- what is the "recursive symbol"
  recurObjSym  : String                   -- what string shld be used to repr
  extractRes   : ResExtractor := default  -- e.g. typing judgements, the type
  mkJudgeObj   : MkJudgeObj   := default  -- makes what judgement is applied to
  mkConclusion : Conclusion   := default  -- assembles conclusion for rule

-- todo monadify
structure InferenceRule.Style where
  judgements  : List Judgement            -- list of judgments that can be used
  tyDefaults  : TyDefault      := default -- default names for objects
  tyAnte      : TyAnte         := default -- what should be included as premise

def InferenceRule.Judgement.expr : InferenceRule.Judgement :=
  { recurTySym  := [``Tst.Expr, ``Tst.Expr.NoContract, ``Tst.Expr.NoResult]
  , recurObjSym := "e"
  }

def InferenceRule.Judgement.lval : InferenceRule.Judgement :=
  { recurTySym  := [``Tst.LValue]
  , recurObjSym := "lv"
  }

def InferenceRule.Judgement.anno : InferenceRule.Judgement :=
  { recurTySym   := [ ``Tst.Anno
                    , ``Tst.Anno.Free
                    -- , ``Tst.Anno.Loop      -- including these breaks things because of the List
                    -- , ``Tst.Anno.Function
                    ]
  , recurObjSym  := "anno"
  , extractRes   := fun e => some (e, "") -- no type info don't care
  , mkConclusion := fun a _ => s!"{a} valid"
  }

def InferenceRule.Judgement.stmt : InferenceRule.Judgement :=
  { recurTySym   := [``Tst.Stmt]
  , recurObjSym  := "stmt"
  , mkConclusion := fun a ρ => s!"{a} : [{ρ}]"
  }

def InferenceRule.Judgement.stmt_list : InferenceRule.Judgement :=
  { recurTySym   := [``Tst.Stmt.List]
  , recurObjSym  := "body"
  , mkConclusion := fun a ρ => s!"{a} : [{ρ}]"
  }

def InferenceRule.Style.expr : InferenceRule.Style :=
  { judgements := [.expr] }

def InferenceRule.Style.lval : InferenceRule.Style :=
  { judgements := [.lval, .expr] }

def InferenceRule.Style.anno : InferenceRule.Style :=
  { judgements := [.anno, .expr] }

def InferenceRule.Style.stmt : InferenceRule.Style :=
  { judgements := [.stmt, .stmt_list, .anno, .expr, .lval] }

def InferenceRule.Style.stmt_list : InferenceRule.Style :=
  { judgements := [.stmt_list, .stmt] }

structure InferenceRule where
  name        : String
  antecedents : List String
  consequent  : String
instance : ToString InferenceRule where
  toString rule :=
    let antes := "\n".intercalate rule.antecedents.reverse
    s!"{antes}\n--- ({rule.name})\n{rule.consequent}"

namespace InferenceRule

/- todo this section is a mess -/
def validateCtxSym : Lean.Expr → Option String
  | .fvar ⟨sym⟩ | .const sym _ => some sym.toString
  | _ => none

def consumeJudgementCtx (judge : Judgement) (expr : Lean.Expr)
    : Option String :=
  aux judge.contextSyms.length expr
where aux : Nat → Lean.Expr → Option String
  | 0, _ => some ""
  | 1, .fvar ⟨sym⟩
  | 1, .const sym _ => return sym.toString
  | 1, .app _fn arg => do
    return ← validateCtxSym arg
  | n + 1, .app fn arg => do
    let str₁ ← validateCtxSym arg
    let str₂ ← aux n fn
    return str₂ ++ judge.contextSep ++ str₁
  | _, _ => none

def consumeContext (style : Style) (expr : Lean.Expr) : Option String :=
  aux style.judgements
where aux : List Judgement → Option String
  | []      => none
  | j :: js => consumeJudgementCtx j expr <|> aux js

def checkType (p : Name → Option α) : Lean.Expr → Option α
  | .const declName _ => p declName
  | .app fn arg => checkType p fn <|> checkType p arg
  | .forallE _ ty _ _ => checkType p ty
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

def buildJudgement
    (judge : Judgement)
    (builder : Builder)
    (expr : Lean.Expr)
    : MetaM (Option String) := do
  match ← judge.extractRes expr with
  | some (expr', τ) =>
    match consumeJudgementCtx judge expr' with
    | some ctx_str =>
      let cur := judge.mkJudgeObj builder.name builder.cur.reverse
      let conclusion := judge.mkConclusion cur τ
      return s!"{ctx_str}{judge.tee}{conclusion}"
    | none => none
  | none => none

def findBuildJudgement (style : Style) (builder : Builder)
    : MetaM (Option String) := do
  aux (replaceDeBruijn builder.bindings builder.expr) style.judgements
where aux (expr : Lean.Expr) : List Judgement → MetaM (Option String)
  | [] => none
  | j :: js => (buildJudgement j builder expr) <|> (aux expr js)

def hasJudgement (style : Style) (ty : Lean.Expr) : Option Judgement :=
  aux style.judgements
where aux : List Judgement → Option Judgement
  | [] => none
  | j :: js =>
    if checkType (if · ∈ j.recurTySym then some () else none) ty |>.isSome
    then some j
    else aux js

def buildExpr (style : Style) (name : Name) (acc : Builder)
    (expr : Lean.Expr)
    : MetaM (Option Builder) :=
  match expr with
  | .lam binder ty body _
  | .forallE binder ty body _ => do
    let acc_old := acc
    let acc := { acc with bindings := binder :: acc.bindings
                        , expr := body
                        }
    match hasJudgement style ty with
    | some judge =>
      let e' := s!"{judge.recurObjSym}{acc.rec_comps}"
      let ante_acc :=
        { acc_old with expr := ty
                     , cur  := [e']
                     , name := none
        }
      match ← buildJudgement judge ante_acc
                (replaceDeBruijn ante_acc.bindings ante_acc.expr)
      with
      | some judge =>
        let antecedents := judge :: acc.rule.antecedents
        let rule := { acc.rule with antecedents }
        let cur  := e' :: acc.cur
        let acc  := { acc with rule, cur, rec_comps := acc.rec_comps + 1 }
        buildExpr style name acc body
      | none => return none
    | none =>
      -- if ty.isForall then -- always include foralls if they appear
        -- let str := toString
            -- <| ← ppExpr (replaceDeBruijn acc_old.bindings ty)
        -- let antecedents := (toString binder ++ " : " ++ str) :: acc.rule.antecedents
        -- let rule := { acc.rule with antecedents }
        -- buildExpr style name { acc with rule } body
      -- else
        let is_ante :=
          checkType (if · ∈ style.tyAnte then some () else none) ty
        if is_ante.isSome then
          let ty_str := toString
            <| ← ppExpr (replaceDeBruijn acc_old.bindings ty)
          let str :=
            if binder.isInternal
            then ty_str
            else s!"{toString binder} : {ty_str}"
          let antecedents := str :: acc.rule.antecedents
          let rule := { acc.rule with antecedents }
          buildExpr style name { acc with rule } body
        else
          if let some str := checkType (style.tyDefaults binder) ty then
            buildExpr style name {acc with cur := str :: acc.cur} body
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
    , bindings  := []
    , expr
    , rule      := ⟨name.lastToString, [], ""⟩
    , cur       := []
    , rec_comps := 0
    }
  match ← buildExpr style name builder_init expr with
  | some builder =>
    let judge? ← findBuildJudgement style builder
    match judge? with
    | some judge =>
      return InferenceRule.mk builder.rule.name builder.rule.antecedents judge
    | none =>
      return none
  | none => return none

-- app doesn't work
private def exprs      := getIndConsNames ``Tst.Expr
private def lvals      := getIndConsNames ``Tst.LValue
private def annos      := getIndConsNames ``Tst.Anno
private def stmts      := getIndConsNames ``Tst.Stmt
private def stmts_list := getIndConsNames ``Tst.Stmt.List

open Typ.Notation

/- todo think if there's a way to automate this?

maybe we should accumulate "keywords" as we move thru the Lean.Expr
and then any variables that aren't bound are pretty-printed to have
`\texttt{...}` at the very least?
-/
private def latexify (str : String) : String :=
  str.replace "Δ" "\\Delta"
  |>.replace "Γ" "\\Gamma"
  |>.replace " " "\\;"
  |>.replace "{" "\\{"
  |>.replace "}" "\\}"
  |>.replace "GCtx.struct" "\\texttt{GCtx.struct}"
  |>.replace "FCtx.updateVar" "\\texttt{FCtx.updateVar}"
  |>.replace "Typ.is_eqtype" "\\texttt{is_eqtype}"
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
  |>.replace "requires" "\\texttt{requires}"
  |>.replace "ensures" "\\texttt{ensures}"
  |>.replace "loop_invariant" "\\texttt{loop_invariant}"
  |>.replace "assert" "\\texttt{assert}"
  |>.replace "//@" "\\texttt{//@}"
  |>.replace "decl_init" "\\texttt{decl_init}"
  |>.replace "decl" "\\texttt{decl}"
  |>.replace "if" "\\texttt{if}"
  |>.replace "while" "\\texttt{while}"
  |>.replace "return_void" "\\texttt{return}"
  |>.replace "return_tau" "\\texttt{return}"
  |>.replace "return" "\\texttt{return}"
  |>.replace "error" "\\texttt{error}"
  |>.replace "nop" "\\texttt{nop}"
  |>.replace "seq" "\\texttt{seq}"
  |>.replace "some" "\\texttt{some}"
  |>.replace "none" "\\texttt{none}"
  |>.replace "valid" "\\textbf{valid}"
  |>.replace "_" "\\_"
  |>.replace "τ" "\\tau"
  |>.replace "ρ" "\\rho"
  |>.replace "₁" "_1"
  |>.replace "₂" "_2"
  |>.replace "₃" "_3"
  |>.replace "⊢" "\\vdash "
  |>.replace "∈" "\\in "
  |>.replace "¬" "\\lnot "
  |>.replace "↑" "\\uparrow "
  |>.replace "Status.Symbol.var" "\\texttt{Status.Symbol.var}"
  |>.replace "Status.Symbol.func" "\\texttt{Status.Symbol.func}"
  |>.replace ".syms" ""
  |>.replace "Typ.equiv" "\\texttt{equiv}"
  |>.replace "UnOp.type" "\\texttt{UnOp.type}"
  |>.replace "Comparator.isEquality" "\\texttt{isEqualityOp}"
  |>.replace "Typ.intersect" "\\texttt{intersect}"
  |>.replace "Typ.Typed.data" ""
  |>.replace "Typ.Typed.type" "\\texttt{type}"
  |>.replace "LValue.is\\_var" "\\texttt{is\\_var}"
  |>.replace "Option.isNone" "\\texttt{isNone}"

def toLaTeX (rule : InferenceRule) : String :=
  let antes_strs := rule.antecedents.map (latexify) |>.reverse
  let antes :=
    if antes_strs = .nil
    then "\\quad"
    else "  \\\\\n    ".intercalate antes_strs
  let conse := latexify rule.consequent
  let name  := latexify rule.name
  s!"\\inferrule
  \{ {antes}\n  }
  \{ {conse} }
  \\; \\textsc\{{name}}"

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
    let name := ``Tst.Stmt.while
    let x ← getConsType name
    IO.println s!"\n\n{x}\n\n{← ppExpr x}"
    let rule? ← InferenceRule.build .stmt name x
    match rule? with
    | some rule =>
      IO.println s!"{rule}"
      IO.println s!"\n\n{rule.toLaTeX}"
    | none =>
      IO.println s!"{x}\n"
      IO.println "Could not build rule {name.toString} :(\n"
      IO.println s!"{← ppExpr x}\n"

-- need to run thru elab to get nice type notation
#eval
  Elab.Command.runTermElabM fun _ => do
    printLaTeX .expr (← exprs)

#eval
  Elab.Command.runTermElabM fun _ => do
    printLaTeX .lval (← lvals)

#eval
  Elab.Command.runTermElabM fun _ => do
    printLaTeX .anno (← annos)

#eval
  Elab.Command.runTermElabM fun _ => do
    printLaTeX .stmt (← stmts)

#eval
  Elab.Command.runTermElabM fun _ => do
    printLaTeX .stmt_list (← stmts_list)
