import Lean
import C0deine.Utils.Comparison
import C0deine.Context.Symbol
import C0deine.Type.Typ
import C0deine.Type.Tst
import Numbers

namespace C0deine.Pst

open Typ
open Numbers

inductive Expr
| num : Numbers.Int32 → Expr
| char : Char → Expr
| str : String → Expr
| var : Symbol → Expr
| «true» : Expr
| «false» : Expr
| null : Expr
| unop_int : Tst.UnOp.Int → Typed Expr → Expr
| unop_bool : Tst.UnOp.Bool → Typed Expr → Expr
| binop_int : Tst.BinOp.Int → Typed Expr → Typed Expr → Expr
| binop_bool : Tst.BinOp.Bool → Typed Expr → Typed Expr → Expr
| binop_eq : Comparator → Typed Expr → Typed Expr → Expr
| binop_rel_int : Comparator → Typed Expr → Typed Expr → Expr
| binop_rel_char : Comparator → Typed Expr → Typed Expr → Expr
| ternop : Typed Expr → Typed Expr → Typed Expr → Expr
| app : Symbol → List (Typed Expr) → Expr
| alloc : Typ → Expr
| alloc_array : Typ → Typed Expr → Expr
| dot : Typed Expr → Symbol → Expr
| deref : Typed Expr → Expr
| index : Typed Expr → Typed Expr → Expr
| result : Expr
| length : Typed Expr → Expr
deriving Inhabited, Lean.ToExpr

inductive LValue
| var : Symbol → LValue
| dot : Typed LValue → Symbol → LValue
| deref : Typed LValue → LValue
| index : Typed LValue → Typed Expr → LValue
deriving Inhabited, Lean.ToExpr

inductive Anno
| requires : Typed Expr → Anno
| ensures : Typed Expr → Anno
| loop_invar : Typed Expr → Anno
| assert : Typed Expr → Anno
deriving Inhabited, Lean.ToExpr

inductive Stmt
| decl : Typed Symbol → List Stmt → Stmt
| decl_init : Typed Symbol → Typed Expr → List Stmt → Stmt
| assign_var : Typed LValue → Typed Expr → Stmt
| assign : Typed LValue → Typed Expr → Stmt
| asnop : Typed LValue → Tst.BinOp.Int → Typed Expr → Stmt
| expr : Typed Expr → Stmt
| ite : Typed Expr → List Stmt → List Stmt → Stmt
| while : Typed Expr → List Anno → List Stmt → Stmt
| return_void : Stmt
| return_tau : Typed Expr → Stmt
| assert : Typed Expr → Stmt
| error : Typed Expr → Stmt
| anno : Anno → Stmt
deriving Inhabited, Lean.ToExpr

structure SDef where
  name : Symbol
  fields : List (Typed Symbol)
deriving Inhabited, Repr, Lean.ToExpr

structure FDecl where
  ret : Option Typ
  name : Symbol
  params : List (Typed Symbol)
  annos : List Anno
deriving Inhabited, Lean.ToExpr

structure FDef extends FDecl where
  body : List Stmt
deriving Inhabited, Lean.ToExpr

inductive GDecl
| fdecl : FDecl → GDecl
| fdef : FDef → GDecl
| sdef : SDef → GDecl
deriving Inhabited, Lean.ToExpr

structure Call where
  name : Symbol
  pure : Bool
deriving Inhabited, Repr, Lean.ToExpr

structure Prog where
  header : List GDecl
  body : List GDecl
  calls : List Call
  strings : List String
deriving Inhabited, Lean.ToExpr

def Expr.ofTst : Tst.Expr Δ Γ τ → Typed Expr
| .num _ i => ⟨τ, .num i⟩
| .char _ c => ⟨τ, .char c⟩
| .str _ s => ⟨τ, .str s⟩
| .var x _ => ⟨τ, .var x⟩
| .true _ => ⟨τ, .true⟩
| .false _ => ⟨τ, .false⟩
| .null _ => ⟨τ, .null⟩
| .unop_int _ _ op e => ⟨τ, .unop_int op (ofTst e)⟩
| .unop_bool _ _ op e => ⟨τ, .unop_bool op (ofTst e)⟩
| .binop_int _ _ _ op l r => ⟨τ, .binop_int op (ofTst l) (ofTst r)⟩
| .binop_bool _ _ _ op l r => ⟨τ, .binop_bool op (ofTst l) (ofTst r)⟩
| .binop_eq _ op _ l r _ _ => ⟨τ, .binop_eq op (ofTst l) (ofTst r)⟩
| .binop_rel_int _ _ _ op _ l r => ⟨τ, .binop_rel_int op (ofTst l) (ofTst r)⟩
| .binop_rel_char _ _ _ op _ l r => ⟨τ, .binop_rel_char op (ofTst l) (ofTst r)⟩
| .ternop _ _ c t f _ => ⟨τ, .ternop (ofTst c) (ofTst t) (ofTst f)⟩
| .app (status:=status) _f _ _ _ args =>
    panic! "Currently, cannot convert function call"
| .alloc τ' => ⟨τ, .alloc τ'⟩
| .alloc_array _ τ' e => ⟨τ, .alloc_array τ' (ofTst e)⟩
| .dot _ e f _ _ => ⟨τ, .dot (ofTst e) f⟩
| .deref _ e => ⟨τ, .deref (ofTst e)⟩
| .index _ _ a i => ⟨τ, .index (ofTst a) (ofTst i)⟩
| .result _ => ⟨τ, .result⟩
| .length _ e => ⟨τ, .length (ofTst e)⟩

def LValue.ofTst : Tst.LValue Δ Γ τ → Typed LValue
| .var x _ => ⟨τ, .var x⟩
| .dot _ lv field _ _ => ⟨τ, .dot (LValue.ofTst lv) field⟩
| .deref _ lv => ⟨τ, .deref (LValue.ofTst lv)⟩
| .index _ _ a i => ⟨τ, .index (LValue.ofTst a) (Expr.ofTst i.val)⟩

def Anno.ofTst : Tst.Anno Δ Γ → Anno
| .requires _ e   => .requires (Expr.ofTst e.val)
| .ensures _ e    => .ensures (Expr.ofTst e)
| .loop_invar _ e => .loop_invar (Expr.ofTst e.val)
| .assert _ e     => .assert (Expr.ofTst e.val)

partial def Stmt.ofTst : Tst.Stmt Δ Γ ρ → Stmt
| .decl name _ body => .decl name (body.toList.map (Stmt.ofTst))
| .decl_init name init _ _ body => .decl_init name (Expr.ofTst init.val) (body.toList.map (Stmt.ofTst))
| .assign_var l _ r _ => .assign_var (LValue.ofTst l) (Expr.ofTst r.val)
| .assign l _ r _ => .assign (LValue.ofTst l) (Expr.ofTst r.val)
| .asnop _ _ l op r => .asnop (LValue.ofTst l) op (Expr.ofTst r.val)
| .expr e => .expr (Expr.ofTst e.val)
| .ite _ c t f => .ite (Expr.ofTst c.val) (t.toList.map (Stmt.ofTst)) (f.toList.map (Stmt.ofTst))
| .while _ c annos body => .while (Expr.ofTst c.val) (annos.map (Anno.ofTst ·.val)) (body.toList.map (Stmt.ofTst))
| .return_void _ => .return_void
| .return_tau _ e => .return_tau (Expr.ofTst e.val)
| .assert _ e => .assert (Expr.ofTst e.val)
| .error _ e => .error (Expr.ofTst e.val)
| .anno a => .anno (Anno.ofTst a.val)

def SDef.ofTst : Tst.SDef → SDef
| ⟨name, field⟩ => ⟨name, field⟩

set_option linter.unusedVariables false in
def FDecl.ofTst : Tst.FDecl Δ → FDecl
| {ret, name, params, init_Γ, annos, initial_init, annos_init} =>
    { ret, name, params, annos := annos.map (Anno.ofTst ·.val)}

set_option linter.unusedVariables false in
def FDef.ofTst : Tst.FDef Δ → FDef
| {ret, name, params, init_Γ, annos, initial_init, annos_init, body, post_init, body_init, body_rets} =>
    { ret, name, params,
      annos := annos.map (Anno.ofTst ·.val),
      body := body.toList.map (Stmt.ofTst)
    }

def Gdecl.ofTst : Tst.GDecl Δ₁ Δ₂ → GDecl
| .fdecl f => .fdecl (FDecl.ofTst f)
| .fdef f => .fdef (FDef.ofTst f)
| .sdef s => .sdef (SDef.ofTst s)

-- TODO!!!
def Prog.ofTst : Tst.Prog → Prog
| { header_ctx, header, body_ctx, body, calls, strings } => {
    header := []
    body := []
    calls := []
    strings := strings
  }

mutual
partial def Expr.toString : Expr → String
| .num i => s!"{i}"
| .char c => s!"'${c}'"
| .str s => s!"\"${s}\""
| .var x => s!"{x}"
| .«true» => "true"
| .«false» => "false"
| .null => "null"
| .unop_int op i => s!"{op} {typedToString i}"
| .unop_bool op b => s!"{op} {typedToString b}"
| .binop_int op l r => s!"{typedToString l} {op} {typedToString r}"
| .binop_bool op l r => s!"{typedToString l} {op} {typedToString r}"
| .binop_eq op l r => s!"{typedToString l} {op} {typedToString r}"
| .binop_rel_int op l r => s!"{typedToString l} {op} {typedToString r}"
| .binop_rel_char op l r => s!"{typedToString l} {op} {typedToString r}"
| .ternop c t f => s!"{typedToString c} ? {typedToString t} : {typedToString f}"
| .app f args => s!"{f}({args.map typedToString |>.concat ", "})"
| .alloc τ => s!"alloc({τ})"
| .alloc_array τ i => s!"alloc_array({τ}, {typedToString i})"
| .dot e f => s!"{typedToString e}.{f}"
| .deref e => s!"{typedToString e}"
| .index a i => s!"{typedToString a}[{typedToString i}]"
| .result => s!"\\result"
| .length e => s!"\\length({typedToString e})"

partial def Expr.typedToString (texpr : Typed Expr) : String :=
  s!"({Expr.toString texpr.data} : {texpr.type})"
end

instance : ToString Expr := ⟨Expr.toString⟩
instance : ToString (Typed Expr) := ⟨Expr.typedToString⟩
instance : Repr Expr := ⟨fun e _ => Expr.toString e⟩
instance : Repr (Typed Expr) := ⟨fun te _ => Expr.typedToString te⟩

def Expr.toTst (τ : Typ) (e : Expr) : Except String (Tst.Expr Δ Γ τ) := do
  match τ, e with
  | .prim .int, .num i => return .num rfl i
  | .prim .char, .char c => return .char rfl c
  | .prim .string, .str s => return .str rfl s
  | τ, .var x =>
    if h : Γ.syms x = some (.var τ) then
      return .var x h
    else throw s!"variable not defined ${x} or does not have type ${τ}"
  | .prim .bool, .true => return .true rfl
  | .prim .bool, .false => return .false rfl
  | .mem (.pointer .any), .null => return .null rfl -- is this correct?
  | .prim .int, .unop_int op ⟨.prim .int, e⟩ =>
    return .unop_int rfl rfl op (← e.toTst (.prim .int))
  | .prim .bool, .unop_bool op ⟨.prim .bool, e⟩ =>
    return .unop_bool rfl rfl op (← e.toTst (.prim .bool))
  | .prim .bool, .binop_eq op ⟨τl, l⟩ ⟨τr, r⟩ =>
    if h₁ : op.isEquality then
      if h₂ : τl.equiv τr then
        if h₃ : τl.is_eqtype ∨ τr.is_eqtype then
          return .binop_eq rfl op h₁ (← l.toTst τl) (← r.toTst τr) h₂ h₃
        else throw s!"binop_eq sides must be an equality type"
      else throw s!"binop_eq sides do not have equivalent types"
    else throw s!"binop_eq operator ${op} is not an equality operator"
  | .prim .bool, .binop_rel_int op ⟨.prim .int, l⟩ ⟨.prim .int, r⟩ =>
    if h : ¬op.isEquality then
      return .binop_rel_int rfl rfl rfl op h (← l.toTst (.prim .int)) (← r.toTst (.prim .int))
    else throw s!"binop_rel_int operator ${op} is an equality operator"
  | .prim .bool, .binop_rel_char op ⟨.prim .char, l⟩ ⟨.prim .char, r⟩ =>
    if h : ¬op.isEquality then
      return .binop_rel_char rfl rfl rfl op h (← l.toTst (.prim .char)) (← r.toTst (.prim .char))
    else throw s!"binop_rel_char operator ${op} is an equality operator"
  | τ, .ternop ⟨.prim .bool, c⟩ ⟨τt, t⟩ ⟨τf, f⟩ => do
    if h₁ : τ = τt.intersect τf then
      if h₂ : τt.equiv τf then
        return .ternop rfl h₁ (← c.toTst (.prim .bool)) (← t.toTst τt) (← f.toTst τf) h₂
      else throw s!"ternop branches not equivalent type"
    else throw "ternop result type doesn't equal intersection of branches"
  | _, .app _f _args => throw "app not implemented"
  | .mem (.pointer τ), .alloc τ' =>
    if τ = τ' then
      return .alloc τ
    else throw "alloc type is not equal"
  | .mem (.array τ), .alloc_array τ' ⟨.prim .int, e⟩ =>
    if τ = τ' then
      return .alloc_array rfl τ (← e.toTst (.prim .int))
    else throw "alloc_array type is not equal"
  | τ, .dot ⟨.mem (.struct s), e⟩ f =>
    match h₁ : Δ.struct s with
    | .some ⟨struct_fields, Bool.true⟩ =>
      if h₂ : struct_fields f = .some τ then
        return .dot rfl (← e.toTst (.mem (.struct s))) f h₁ h₂
      else throw s!"dot expr does not have field ${f} in struct ${s}"
    | .some ⟨_, Bool.false⟩ =>
      throw s!"dot expr type, struct ${s}, isn't defined yet"
    | .none =>
      throw s!"dot expr type is an unknown struct ${s}"
  | τ, .deref ⟨.mem (.pointer τ'), e⟩ =>
    if τ = τ' then
      return .deref rfl (← e.toTst (.mem (.pointer τ)))
    else throw "deref type is not equal"
  | τ, .index ⟨.mem (.array τ'), a⟩ ⟨.prim .int, i⟩ =>
    if τ = τ' then
      return .index rfl rfl (← a.toTst (.mem (.array τ))) (← i.toTst (.prim .int))
    else throw "index type is not equal"
  | τ, .result =>
    if h : Γ.ret = some τ then
      return .result h
    else throw "result type does not match return type"
  | .prim .int, .length ⟨.mem (.array τ'), a⟩ =>
    if τ = τ' then
      return .length rfl (← a.toTst (.mem (.array τ)))
    else throw "length type is not equal"
  | _, _ =>
    throw s!"could not build a TST from the provided type and PST ${e} : ${τ}"

def Expr.toTstNoContract (τ : Typ) (e : Expr) : Except String (Tst.Expr.NoContract Δ Γ τ) := do
  let tst ← e.toTst τ
  -- todo actually check that no contracts are used
  return ⟨tst, sorry⟩

def Expr.toTstNoResult (τ : Typ) (e : Expr) : Except String (Tst.Expr.NoResult Δ Γ τ) := do
  let tst ← e.toTst τ
  -- todo actually check that no results are used
  return ⟨tst, sorry⟩

def LValue.toTst (τ : Typ) (l : LValue) : Except String (Tst.LValue Δ Γ τ) := do
  match τ, l with
  | τ, .var x =>
    if h : Γ.syms x = some (.var τ) then
      return .var x h
    else throw s!"variable not defined ${x} or does not have type ${τ}"
  | τ, .dot ⟨.mem (.struct s), e⟩ f =>
    match h₁ : Δ.struct s with
    | .some ⟨struct_fields, Bool.true⟩ =>
      if h₂ : struct_fields f = .some τ then
        return .dot rfl (← e.toTst (.mem (.struct s))) f h₁ h₂
      else throw s!"dot expr does not have field ${f} in struct ${s}"
    | .some ⟨_, Bool.false⟩ =>
      throw s!"dot expr type, struct ${s}, isn't defined yet"
    | .none =>
      throw s!"dot expr type is an unknown struct ${s}"
  | τ, .deref ⟨.mem (.pointer τ'), e⟩ =>
    if τ = τ' then
      return .deref rfl (← e.toTst (.mem (.pointer τ)))
    else throw "deref type is not equal"
  | τ, .index ⟨.mem (.array τ'), a⟩ ⟨.prim .int, i⟩ =>
    if τ = τ' then
      return .index rfl rfl (← a.toTst (.mem (.array τ))) (← i.toTstNoContract (.prim .int))
    else throw "index type is not equal"
  | _, _ =>
    throw s!"could not build a TST from the provided type and PST lvalue"

def Anno.toTst (a : Anno) : Except String (Tst.Anno Δ Γ) := do
  match a with
  | .requires ⟨.prim .bool, e⟩    => return .requires rfl (← e.toTstNoResult (.prim .bool))
  | .ensures ⟨.prim .bool, e⟩     => return .ensures rfl (← e.toTst (.prim .bool))
  | .loop_invar ⟨.prim .bool, e⟩  => return .loop_invar rfl (← e.toTstNoResult (.prim .bool))
  | .assert ⟨.prim .bool, e⟩      => return .assert rfl (← e.toTstNoResult (.prim .bool))
  | _ => throw "type of anno expression is not bool"

def Anno.Function.toTst (a : Anno) : Except String (Tst.Anno.Function Δ Γ) := do
  let res ← Anno.toTst a
  if h : Tst.Anno.function res then return ⟨res, h⟩
  else throw "expected a function annotation"

partial def Stmt.toTst (Γ : Tst.FCtx) (s : Stmt) : Except String (Tst.Stmt Δ Γ ρ) := do
  match s with
  | .decl x body =>
    let Γ' := Γ.updateVar x.data x.type
    let newBody ← body.foldlM (fun acc s => do return (← s.toTst Γ') :: acc) []
    return .decl x rfl (Tst.Stmt.List.ofList newBody.reverse)
  | .decl_init x ⟨τ, e⟩ body =>
    let Γ' := Γ.updateVar x.data x.type
    let tstBody ← body.foldlM (fun acc s => do return (← s.toTst Γ') :: acc) []
    let tstExpr ← e.toTstNoContract τ
    if h : x.type.equiv τ then
      return .decl_init x tstExpr h rfl (Tst.Stmt.List.ofList tstBody.reverse)
    else throw "variable and init expr types do not match"
  | .assign_var ⟨τl, l⟩ ⟨τe, e⟩ =>
    let tstLval ← l.toTst τl
    let tstExpr ← e.toTstNoContract τe
    if h₁ : tstLval.is_var then
      if h₂ : τl.equiv τe then
        return .assign_var tstLval h₁ tstExpr h₂
      else throw "assign_var lval and expr types not equiv"
    else throw "assign_var lval is not a var"
  | .assign ⟨τl, l⟩ ⟨τe, e⟩ =>
    let tstLval ← l.toTst τl
    let tstExpr ← e.toTstNoContract τe
    if h₁ : ¬tstLval.is_var then
      if h₂ : τl.equiv τe then
        return .assign tstLval h₁ tstExpr h₂
      else throw "assign lval and expr types not equiv"
    else throw "assign lval is a var"
  | .asnop ⟨.prim .int, l⟩ op ⟨.prim .int, e⟩ =>
    let tstLval ← l.toTst (.prim .int)
    let tstExpr ← e.toTstNoContract (.prim .int)
    return .asnop rfl rfl tstLval op tstExpr
  | .expr ⟨τe, e⟩ =>
    return .expr (← e.toTstNoContract τe)
  | .ite ⟨.prim .bool, c⟩ t f =>
    let tstCond ← c.toTstNoContract (.prim .bool)
    let tstTrue ← t.foldlM (fun acc s => do return (← s.toTst Γ) :: acc) []
    let tstFalse ← f.foldlM (fun acc s => do return (← s.toTst Γ) :: acc) []
    return .ite rfl tstCond
      (Tst.Stmt.List.ofList tstTrue.reverse)
      (Tst.Stmt.List.ofList tstFalse.reverse)
  | .while ⟨.prim .bool, c⟩ annos body =>
    let tstCond ← c.toTstNoContract (.prim .bool)
    let tstAnnos ← annos.foldlM (s := List (Tst.Anno.Loop Δ Γ)) (fun acc a => do
        let tst ← a.toTst
        if h : tst.loop then
          return ⟨tst, h⟩ :: acc
        else throw "while annotations must only be loop invariant"
      ) []
    let tstBody ← body.foldlM (fun acc s => do return (← s.toTst Γ) :: acc) []
    return .while rfl tstCond (tstAnnos.reverse) (Tst.Stmt.List.ofList tstBody.reverse)
  | .return_void =>
    if h : ρ.isNone then
      return .return_void h
    else throw s!"return_void but function has return type ${ρ}"
  | .return_tau ⟨τe, e⟩ =>
    let tst ← e.toTstNoContract τe
    if h : equiv_opt ρ (some τe) then
      return .return_tau sorry tst
    else throw "return_tau expression type not same as return type"
  | .assert ⟨.prim .bool, e⟩ =>
    return .assert rfl (← e.toTstNoContract (.prim .bool))
  | .error ⟨.prim .string, e⟩ =>
    return .error rfl (← e.toTstNoContract (.prim .string))
  | .anno a =>
    let tstAnno ← a.toTst
    if h : tstAnno.free then
      return .anno ⟨tstAnno, h⟩
    else throw "can only use assert annotations in statements"
  | _ => throw "could not build a TST from the provided type and PST stmt"

def SDef.toTst : SDef → Tst.SDef
| ⟨name, field⟩ => ⟨name, field⟩

-- set_option linter.unusedVariables false in
def FDecl.toTst : FDecl → Except String (Tst.FDecl Δ)
| { ret, name, params, annos } => do
    return {
      ret
      name
      params
      annos := ← annos.mapM (Anno.Function.toTst ·)
      init_Γ := Tst.FCtx.init Δ ret params
      annos_init := sorry
    }

set_option linter.unusedVariables false in
def FDef.toTst : FDef → Except String (Tst.FDef Δ)
| { ret, name, params, annos, body } => do
    let init_Γ := Tst.FCtx.init Δ ret params
    let Γ := init_Γ.addFunc name (Typ.flattenOpt ret) params
    return {
      ret,
      name,
      params,
      annos := ← annos.mapM (Anno.Function.toTst ·),
      body := .ofList <| ← body.mapM (Stmt.toTst Γ)
      init_Γ
      annos_init := sorry
      post_init := sorry
      body_init := sorry
      body_rets := sorry
    }
