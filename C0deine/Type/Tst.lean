/- C0deine - TST
   A Typed Syntax Tree, which is similar to the AST, but with expressions
   having typed annotations. Types are dealiased in this representation.
   - Thea Brick
 -/
import Numbers
import C0deine.AuxDefs
import C0deine.Type.Typ
import C0deine.Context.Symbol
import C0deine.Utils.Comparison

namespace C0deine.Tst

open Typ

inductive UnOp.Int  | neg | not deriving Inhabited
inductive UnOp.Bool | neg       deriving Inhabited
inductive UnOp
| int (op : UnOp.Int)
| bool (op : UnOp.Bool)
deriving Inhabited

inductive BinOp.Int
| plus | minus | times | div | mod | and | xor | or | lsh | rsh
deriving Inhabited

inductive BinOp.Bool
| and | or
deriving Inhabited

inductive BinOp
| int (op : BinOp.Int)
| cmp (op : Comparator)
| bool (op : BinOp.Bool)
deriving Inhabited

@[inline] def UnOp.type : UnOp → Typ
  | .int _  => .prim .int
  | .bool _ => .prim .bool

@[inline] private def int    := Typ.prim .int
@[inline] private def bool   := Typ.prim .bool
@[inline] private def ptr    := Typ.mem ∘ .pointer
@[inline] private def arr    := Typ.mem ∘ .array
@[inline] private def struct := Typ.mem ∘ .struct


structure FuncSig where
  arity  : Nat
  argTys : Fin arity → Typ
  retTy  : Typ    -- use .any  if void

structure Status.Var where
  type        : Typ
  initialised : Bool

structure StructSig where
  fieldTys : Symbol → Option Typ

structure Status.Func where
  type    : FuncSig
  defined : Bool

structure Status.Struct where
  sig     : StructSig
  defined : Bool

inductive Status.Symbol
| var   (v : Status.Var)
| func  (f : Status.Func)
| alias (t : Typ)

abbrev FCtx := Symbol → Option Status.Symbol

@[inline] def FCtx.update (Γ : FCtx) (x : Symbol) (s : Status.Symbol) : FCtx :=
  Function.update Γ x (some s)
@[inline] def FCtx.updateVar (Γ : FCtx) (x : Symbol) (s : Status.Var) : FCtx :=
  Γ.update x (.var s)
@[inline] def FCtx.updateFunc
    (Γ : FCtx) (x : Symbol) (s : Status.Func) : FCtx :=
  Γ.update x (.func s)
@[inline] def FCtx.ofParams (params : List (Typed Symbol)) : FCtx :=
  (params.map (fun p => (p.data, Tst.Status.Symbol.var ⟨p.type, true⟩))).toMap
@[inline] def FCtx.addFunc
    (Γ : FCtx) (f : Symbol) (retTy : Typ) (params : List (Typed Symbol))
    : FCtx :=
  let params_Γ := FCtx.ofParams params
  let args := fun i => params.get i |>.type
  let status := ⟨⟨params.length, args, retTy⟩, true⟩
  fun x => -- re-add params bc they shadow the function definition
    match params_Γ x with
    | some status => some status
    | none => if x = f then some (.func status) else Γ x
@[inline] def FCtx.initialiseAll (Γ : FCtx) : FCtx :=
  fun x =>
    match Γ x with
    | .some (.var status) => .some (.var {status with initialised := true})
    | status => status

structure GCtx where
  symbols : Symbol → Option Status.Symbol := fun _ => none
  struct  : Symbol → Option StructSig     := fun _ => none
deriving Inhabited

@[inline] def FCtx.init
    (Δ : GCtx) (params : List (Typed Symbol)) : FCtx :=
  let params_Γ := FCtx.ofParams params
  fun x =>
    match params_Γ x with
    | some status => some status
    | none => Δ.symbols x

inductive Expr (Δ : GCtx) (Γ : FCtx) : Typ → Type
| num     : Int32  → Expr Δ Γ int
| char    : Char   → Expr Δ Γ (.prim .char)
| str     : String → Expr Δ Γ (.prim .string)
| var     : (x : Symbol) → Γ x = .some (.var ⟨τ, true⟩) → Expr Δ Γ τ
| «true»  : Expr Δ Γ bool
| «false» : Expr Δ Γ bool
| null    : Expr Δ Γ (ptr .any)
| unop
  : (op : UnOp)
  → τ.equiv op.type
  → (e : Expr Δ Γ τ)
  → Expr Δ Γ op.type
| binop_int
  : {τ₁ : {τ : Typ // τ = int}}
  → {τ₂ : {τ : Typ // τ = int}}
  → (op : BinOp.Int)
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ int
| binop_bool
  : {τ₁ : {τ : Typ // τ = bool}}
  → {τ₂ : {τ : Typ // τ = bool}}
  → (op : BinOp.Bool)
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ bool
| binop_eq
  : (op : Comparator)
  → op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → τ₁.equiv τ2
  → τ₁.is_eqtype ∨ τ₂.is_eqtype
  → Expr Δ Γ bool
| binop_rel₁
  : {τ₁ : {τ : Typ // τ = int}}
  → {τ₂ : {τ : Typ // τ = int}}
  → (op : Comparator)
  → ¬op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ bool
| binop_rel₂
  : {τ₁ : {τ : Typ // τ = char}}
  → {τ₂ : {τ : Typ // τ = char}}
  → (op : Comparator)
  → ¬op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ bool
| ternop
  : {τ₁ : {τ : Typ // τ = bool}}
  → (cond : Expr Δ Γ τ₁)
  → (tt : Expr Δ Γ τ₂)
  → (ff : Expr Δ Γ τ₃)
  → τ₂.equiv τ₃
  → Expr Δ Γ (τ₂.intersect τ₃)
| app
  : (f : Symbol)
  → Γ f = .some (.func status)
  → (τs : Fin status.type.arity → Typ)
  → (eq : ∀ i, (status.type.argTys i).equiv (τs i))
  → (args : (i : Fin status.type.arity) → Expr Δ Γ (τs i))
  → Expr Δ Γ status.type.retTy
| alloc : (τ : Typ) → Expr Δ Γ (ptr τ)
| alloc_array
  : {τ₁ : {τ : Typ // τ = int}}
  → (τ : Typ)
  → Expr Δ Γ τ₁
  → Expr Δ Γ (arr τ)
| dot
  : {τ₁ : {τ : Typ // τ = struct s}}
  → Expr Δ Γ τ₁
  → (field : Symbol)
  → Δ.struct s = .some str
  → str.fieldTys field = .some τ
  → Expr Δ Γ τ
| deref
  : {τ₁ : {τ' : Typ // τ' = ptr τ}}
  → Expr Δ Γ τ₁
  → Expr Δ Γ τ
| index
  : {τ₁ : {τ' : Typ // τ' = arr τ}}
  → {τ₂ : {τ : Typ // τ = int}}
  → Expr Δ Γ τ₁
  → Expr Δ Γ τ₂
  → Expr Δ Γ τ
| result : Expr Δ Γ τ
| length
  : {τ₁ : {τ' : Typ // τ' = arr τ}}
  → Expr Δ Γ τ₁
  → Expr Δ Γ int

@[inline] def Expr.typeWith {p : Typ → Prop} (e : Expr Δ Γ τ) (h : p τ)
    : Expr Δ Γ (⟨τ, h⟩ : {τ : Typ // p τ}) := e
@[inline] def Expr.typeWithEq {τ₂ : Typ} (e : Expr Δ Γ τ) (eq : τ = τ₂)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = τ₂}) :=
  e.typeWith (p := fun t => t = τ₂) eq
@[inline] def Expr.typeWithEquiv {τ₂ : Typ} (e : Expr Δ Γ τ) (eq : τ.equiv τ₂)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ.equiv τ₂}) :=
  e.typeWith (p := fun t => t.equiv τ₂) eq

@[inline] def Expr.intType (e : Expr Δ Γ τ) (eq : τ = int)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = int}) := e.typeWithEq eq
@[inline] def Expr.boolType (e : Expr Δ Γ τ) (eq : τ = bool)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = bool}) := e.typeWithEq eq
@[inline] def Expr.charType (e : Expr Δ Γ τ) (eq : τ = .prim .char)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = .prim .char}) := e.typeWithEq eq
@[inline] def Expr.stringType (e : Expr Δ Γ τ) (eq : τ = .prim .string)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = .prim .string}) := e.typeWithEq eq
@[inline] def Expr.ptrType (e : Expr Δ Γ τ) (τ' : Typ) (eq : τ = ptr τ')
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = ptr τ'}) := e.typeWithEq eq
@[inline] def Expr.arrType (e : Expr Δ Γ τ) (τ' : Typ) (eq : τ = arr τ')
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = arr τ'}) := e.typeWithEq eq
@[inline] def Expr.structType (e : Expr Δ Γ τ) (s : Symbol) (eq : τ = struct s)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = struct s}) := e.typeWithEq eq

/- Assert that some predicate P applies to every subexpression -/
inductive Expr.All (P : {τ : Typ} → Expr Δ Γ τ → Bool) : Expr Δ Γ τ → Prop
| num     : P (.num   v) → All P (.num   v)
| char    : P (.char  c) → All P (.char  c)
| str     : P (.str   s) → All P (.str   s)
| var     : P (.var h x) → All P (.var h x)
| «true»  : P (.true   ) → All P (.true  )
| «false» : P (.false  ) → All P (.false )
| null    : P (.null   ) → All P (.null  )
| unop
  : All P e
  → P (.unop op eq e)
  → All P (.unop op eq e)
| binop_int
  : All P l
  → All P r
  → P (.binop_int op l r)
  → All P (.binop_int op l r)
| binop_bool
  : All P l
  → All P r
  → P (.binop_bool op l r)
  → All P (.binop_bool op l r)
| binop_eq
  : All P l
  → All P r
  → P (.binop_eq op eq l r h₁ h₂)
  → All P (.binop_eq op eq l r h₁ h₂)
| binop_rel₁
  : All P l
  → All P r
  → P (.binop_rel₁ op eq l r)
  → All P (.binop_rel₁ op eq l r)
| binop_rel₂
  : All P l
  → All P r
  → P (.binop_rel₂ op eq l r)
  → All P (.binop_rel₂ op eq l r)
| ternop
  : All P cc
  → All P tt
  → All P ff
  → P (.ternop cc tt ff h₂)
  → All P (.ternop cc tt ff h₂)
| app
  : {hsig : Γ f = .some (.func status)}
  → {args : (i : Fin status.type.arity) → Expr Δ Γ (τs i)}
  → (∀ i, All P (args i))
  → P (.app f hsig τs eq args)
  → All P (.app f hsig τs eq args)
| alloc : P (.alloc τ₁) → All P (.alloc τ₁)
| alloc_array
  : All P e
  → P (.alloc_array τ₁ e)
  → All P (.alloc_array τ₁ e)
| dot
  : All P e
  → P (.dot e f h₁ h₂)
  → All P (.dot e f h₁ h₂)
| deref
  : All P e
  → P (.deref e)
  → All P (.deref e)
| index
  : All P e
  → All P indx
  → P (.index e indx)
  → All P (.index e indx)
| result
  : P .result
  → All P (.result)
| length
  : All P e
  → P (.length e)
  → All P (.length e)

@[inline] def Expr.OnlyContract : Expr Δ Γ τ → Bool
  | .result   => .true
  | .length _ => .true
  | _         => .false
@[inline] def Expr.IsResult : Expr Δ Γ τ → Bool
  | .result => .true
  | _       => .false

@[inline] def Expr.no_contract : Expr Δ Γ τ → Bool :=
  .not ∘ Tst.Expr.OnlyContract
@[inline] def Expr.no_result   : Expr Δ Γ τ → Bool :=
  .not ∘ Tst.Expr.IsResult
abbrev Expr.NoContract Δ Γ τ := {e : Expr Δ Γ τ // Expr.All no_contract e}
abbrev Expr.NoResult   Δ Γ τ := {e : Expr Δ Γ τ // Expr.All no_result   e}

abbrev TExpr := {Δ : GCtx} → {Γ : FCtx} → {τ : Typ} → Expr Δ Γ τ

inductive LValue (Δ : GCtx) (Γ : FCtx) : Typ → Type
| var   : (x : Symbol)
        → (Γ x = .some (.var ⟨τ, true⟩)) ∨ (Γ x = .some (.var ⟨τ, false⟩))
        → LValue Δ Γ τ
| dot   : {τ₁ : {τ : Typ // τ = struct s}}
        → LValue Δ Γ τ₁
        → (field : Symbol)
        → Δ.struct s = .some str
        → str.fieldTys field = .some τ
        → LValue Δ Γ τ
| deref : {τ₁ : {τ' : Typ // τ' = ptr τ}}
        → LValue Δ Γ τ₁
        → LValue Δ Γ τ
| index : {τ₁ : {τ' : Typ // τ' = arr τ}}
        → {τ₂ : {τ : Typ // τ = int}}
        → LValue Δ Γ τ₁
        → Expr.NoContract Δ Γ τ₂
        → LValue Δ Γ τ

@[inline] def LValue.typeWith {p : Typ → Prop} (e : LValue Δ Γ τ) (h : p τ)
    : LValue Δ Γ (⟨τ, h⟩ : {τ : Typ // p τ}) := e
@[inline] def LValue.typeWithEq {τ₂ : Typ} (e : LValue Δ Γ τ) (eq : τ = τ₂)
    : LValue Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = τ₂}) :=
  e.typeWith (p := fun t => t = τ₂) eq

@[inline] def LValue.intType (e : LValue Δ Γ τ) (eq : τ = int)
    : LValue Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = int}) := e.typeWithEq eq
@[inline] def LValue.ptrType (e : LValue Δ Γ τ) (τ' : Typ) (eq : τ = ptr τ')
    : LValue Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = ptr τ'}) := e.typeWithEq eq
@[inline] def LValue.arrType (e : LValue Δ Γ τ) (τ' : Typ) (eq : τ = arr τ')
    : LValue Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = arr τ'}) := e.typeWithEq eq
@[inline] def LValue.structType (e : LValue Δ Γ τ) (s : Symbol) (eq : τ = struct s)
    : LValue Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = struct s}) := e.typeWithEq eq

inductive Anno (Δ : GCtx) (Γ : FCtx) : Type
| requires   : {τ : {τ : Typ // τ = bool}} → Expr.NoResult Δ Γ τ → Anno Δ Γ
| ensures    : {τ : {τ : Typ // τ = bool}} → Expr          Δ Γ τ → Anno Δ Γ
| loop_invar : {τ : {τ : Typ // τ = bool}} → Expr.NoResult Δ Γ τ → Anno Δ Γ
| assert     : {τ : {τ : Typ // τ = bool}} → Expr.NoResult Δ Γ τ → Anno Δ Γ

-- only requires/ensures can annotate functions
@[inline, reducible] def Anno.function : Anno Δ Γ → Bool
  | .requires _   => true
  | .ensures _    => true
  | .loop_invar _ => false
  | .assert _     => false

-- only loop_invariant and assert can annotate loops
@[inline, reducible] def Anno.loop : Anno Δ Γ  → Bool
  | .requires _   => false
  | .ensures _    => false
  | .loop_invar _ => true
  | .assert _     => false -- see language deviation

-- only assert can be not attatched to a loop/function
@[inline, reducible] def Anno.free : Anno Δ Γ  → Bool
  | .requires _   => false
  | .ensures _    => false
  | .loop_invar _ => false
  | .assert _     => true

abbrev Anno.Loop     Δ Γ := {a : Anno Δ Γ  // Anno.loop     a}
abbrev Anno.Function Δ Γ := {a : Anno Δ Γ  // Anno.function a}
abbrev Anno.Free     Δ Γ := {a : Anno Δ Γ  // Anno.free     a}

mutual
inductive Stmt (Δ : GCtx) : (Γ : FCtx) → Option Typ → Type
| decl
  : (name : Typed Symbol)
  → (new_ctx : Γ' = Γ.updateVar name.data ⟨name.type, false⟩)
  → (body : Stmt.List Δ Γ' ρ)
  → Stmt Δ Γ ρ
| decl_init
  : (name : Typed Symbol)
  → (init : Expr.NoContract Δ Γ τ)
  → (ty_equiv : name.type.equiv τ)
  → (new_ctx : Γ' = Γ.updateVar name.data ⟨name.type, true⟩)
  → (body : Stmt.List Δ Γ' ρ)
  → Stmt Δ Γ ρ
| assign_var
  : (lhs : LValue Δ Γ τ₁)
  → (is_var : lhs = .var name h)
  → (rhs : Expr.NoContract Δ Γ τ₂)
  → (ty_equiv : τ₁.equiv τ₂)
  → (new_ctx : Γ' = Γ.updateVar name ⟨τ₁, true⟩)
  → (body : Stmt.List Δ Γ' ρ)
  → Stmt Δ Γ ρ
| assign
  : (lhs : LValue Δ Γ τ₁)
  → (is_var : ∀ name h, lhs ≠ .var name h) -- elaborate away
  → (rhs : Expr.NoContract Δ Γ τ₂)
  → (ty_equiv : τ₁.equiv τ₂)
  → Stmt Δ Γ ρ
| asnop
  : {τ₁ : {τ : Typ // τ = int}}
  → {τ₂ : {τ : Typ // τ = int}}
  → (lhs : LValue Δ Γ τ₁)
  → BinOp.Int
  → (rhs : Expr.NoContract Δ Γ τ₂)
  → Stmt Δ Γ ρ
| expr
  : Expr.NoContract Δ Γ τ
  → Stmt Δ Γ ρ
| ite
  : {τ : {τ : Typ // τ = bool}}
  → (cond : Expr.NoContract Δ Γ τ)
  → (tt : Stmt.List Δ Γ ρ)
  → (ff : Stmt.List Δ Γ ρ)
  → Stmt Δ Γ ρ
| while
  : {τ : {τ : Typ // τ = bool}}
  → (cond : Expr.NoContract Δ Γ τ)
  → List (Anno.Loop Δ Γ)
  → Stmt.List Δ Γ ρ
  → Stmt Δ Γ ρ
| return_void : Stmt Δ Γ none
| return_tau
  : {τ₁ : {τ' : Typ // τ' = τ }}
  → Expr.NoContract Δ Γ τ₁
  → Stmt Δ Γ (some τ)
| assert
  : {τ : {τ : Typ // τ = bool}}
  → Expr.NoContract Δ Γ τ
  → Stmt Δ Γ ρ
| error
  : {τ : {τ : Typ // τ = .prim .string}}
  → Expr.NoContract Δ Γ τ
  → Stmt Δ Γ ρ
| anno : Anno.Free Δ Γ → Stmt Δ Γ ρ

inductive Stmt.List (Δ : GCtx) : (Γ : FCtx) → Option Typ → Type
| nil  : Stmt.List Δ Γ ρ
| cons : (s : Stmt Δ Γ ρ) → Stmt.List Δ Γ ρ → Stmt.List Δ Γ ρ
end

def Stmt.List.toList : Stmt.List Δ Γ ρ → _root_.List (Stmt Δ Γ ρ)
  | .nil => []
  | .cons stmt stmts => stmt :: toList stmts

def Stmt.List.ofList : _root_.List (Stmt Δ Γ ρ) → Stmt.List Δ Γ ρ
  | [] => .nil
  | stmt :: stmts => cons stmt (ofList stmts)

instance : Coe (Stmt.List Δ Γ ρ) (List (Stmt Δ Γ ρ)) := ⟨Stmt.List.toList⟩

structure SDef where
  name : Symbol
  fields : List (Typed Symbol)


structure FDecl (Δ : GCtx) where
  ret    : Option Typ
  name   : Symbol
  params : List (Typed Symbol)
  init_Γ : FCtx
  annos  : List (Anno.Function Δ init_Γ)

structure FDef (Δ : GCtx) extends FDecl Δ where
  body : List (Stmt Δ (init_Γ.addFunc name (Typ.flattenOpt ret) params) ret)

def GCtx.updateStruct (Δ : GCtx) (s : SDef) : GCtx :=
  let sig := ⟨Typed.toMap s.fields⟩
  { Δ with struct := Function.update Δ.struct s.name (some sig) }

def GCtx.updateFunc (Δ : GCtx) (f : FDecl Δ) (defined : Bool) : GCtx :=
  let arity  := f.params.length
  let argTys := fun i => (f.params.get i).type
  let retTy := match f.ret with | none => .any | some τ => τ

  let defined' := -- can declare a function after defining it
    if let some (.func status) := Δ.symbols f.name then
      defined || status.defined
    else defined

  let sig : Status.Func := ⟨⟨arity, argTys, retTy⟩, defined'⟩
  { Δ with symbols := FCtx.updateFunc Δ.symbols f.name sig}

inductive GDecl (Δ : GCtx) : GCtx → Type
| fdecl : (f : FDecl Δ) → GDecl Δ (Δ.updateFunc f false)
| fdef  : (f : FDef Δ)  → GDecl Δ (Δ.updateFunc f.toFDecl true)
| sdef  : (s : SDef)    → GDecl Δ (Δ.updateStruct s)

inductive GDecl.List : GCtx → GCtx → Type
| nil    : GDecl.List Δ Δ
| cons   : GDecl.List Δ₁ Δ₂ → (g : GDecl Δ₂ Δ₃) → GDecl.List Δ₁ Δ₃
| update : GDecl.List Δ₁ Δ₂ → GDecl.List Δ₁ Δ₃

/- Functions calls that a program makes
    True means the call is used in a contract, so the function must be pure.
-/
def Calls := Symbol.Map Bool

def Calls.merge (calls1 calls2 : Calls) : Calls :=
  calls1.mergeWith (fun _ x y => x || y) calls2


structure Prog where
  header_ctx : GCtx
  header     : GDecl.List {} header_ctx
  body_ctx   : GCtx
  body       : GDecl.List header_ctx body_ctx
  calls      : Calls
  strings    : List String


def UnOp.Int.toString : UnOp.Int → String
  | neg => "~"
  | not => "!"
instance : ToString UnOp.Int where toString := UnOp.Int.toString

def UnOp.Bool.toString : UnOp.Bool → String
  | neg => "!"
instance : ToString UnOp.Bool where toString := UnOp.Bool.toString

def UnOp.toString : UnOp → String
  | int op  => s!"{op}"
  | bool op => s!"{op}"
instance : ToString UnOp where toString := UnOp.toString


def BinOp.Int.toString : BinOp.Int → String
  | plus => "+"
  | minus => "-"
  | times => "*"
  | div => "/"
  | mod => "%"
  | and => "&"
  | xor => "^"
  | or => "|"
  | lsh => "<<"
  | rsh => ">>"
instance : ToString BinOp.Int where toString := BinOp.Int.toString

def BinOp.Bool.toString : BinOp.Bool → String
  | .and => "&&"
  | .or  => "||"
instance : ToString BinOp.Bool where toString := BinOp.Bool.toString

def BinOp.toString : BinOp → String
  | int op  => s!"{op}"
  | cmp op  => s!"{op}"
  | bool op => s!"{op}"
instance : ToString BinOp where toString := BinOp.toString

def Expr.toString : Expr Δ Γ τ → String
  | .num v       => s!"({v} : {τ})"
  | .char c      => s!"('{c}' : {τ})"
  | .str s       => s!"(\"{s}\" : {τ})"
  | .«true»      => s!"(true : {τ})"
  | .«false»     => s!"(false : {τ})"
  | .null        => s!"(NULL : {τ})"
  | .unop op _ e => s!"({op}{Expr.toString e} : {τ})"
  | .binop_int op l r
  | .binop_bool op l r
  | .binop_eq op _ l r _ _
  | .binop_rel₁ op _ l r
  | .binop_rel₂ op _ l r =>
    s!"({Expr.toString l} {op} {Expr.toString r} : {τ})"
  | .ternop cc tt ff _ =>
    s!"({Expr.toString cc} ? {Expr.toString tt} : {Expr.toString ff} : {τ})"
  | .app f _ _ _ args =>
    let str_args := ", ".intercalate
      (.ofFn (fun i => Expr.toString (args i)))
    s!"({f}({str_args}) : {τ})"
  | .alloc ty => s!"(alloc({ty}) : {τ})"
  | .alloc_array ty e => s!"(alloc_array({ty}, {Expr.toString e}) : {τ})"
  | .var name _ => s!"({name} : {τ})"
  | .dot e field _ _ => s!"({Expr.toString e}.{field} : {τ})"
  | .deref e   => s!"(*{Expr.toString e} : {τ})"
  | .index e i => s!"({Expr.toString e}[{Expr.toString i}] : {τ})"
  | .result    => s!"(\\result : {τ})"
  | .length e  => s!"(\\length {Expr.toString e} : {τ})"

instance : ToString (Expr Δ Γ τ) := ⟨Expr.toString⟩

def Anno.toString : Anno Δ Γ → String
  | .requires e   => s!"//@requires {e}"
  | .ensures e    => s!"//@ensures {e}"
  | .loop_invar e => s!"//@loop_invariant {e}"
  | .assert e     => s!"//@assert {e}"
instance : ToString (Anno Δ Γ) := ⟨Anno.toString⟩
def Anno.listToString : List (Anno Δ Γ) → String
  | [] => ""
  | as => String.intercalate "\n  " (as.map Anno.toString) ++ "\n  "
instance : ToString (List (Anno Δ Γ)) := ⟨Anno.listToString⟩
instance : ToString (List (Anno.Function Δ Γ)) :=
  ⟨Anno.listToString ∘ .map (·.val)⟩
instance : ToString (List (Anno.Loop Δ Γ)) :=
  ⟨Anno.listToString ∘ .map (·.val)⟩
instance : ToString (List (Anno.Free Δ Γ)) :=
  ⟨Anno.listToString ∘ .map (·.val)⟩

def LValue.toString : LValue Δ Γ τ → String
  | .var name _ => s!"({name} : {τ})"
  | .dot e field _ _ =>
    s!"({LValue.toString e}.{field} : {τ})"
  | .deref e => s!"(*{LValue.toString e} : {τ})"
  | .index e i => s!"({LValue.toString e}[{i}] : {τ})"

instance : ToString (LValue Δ Γ τ) where toString := LValue.toString
instance : ToString (List (Typed Symbol)) where
  toString tss := tss.map Typed.toString |> String.intercalate ", "

mutual
partial def Stmt.toString (s : Stmt Δ Γ ρ) : String :=
  match s with
  | .decl name _ body =>
    let str_body := (Stmt.listToString body).replace "\n" "\n  "
    s!"declare({name},\n  {str_body}\n)"
  | .decl_init name init _ _ body =>
    let str_body := (Stmt.listToString body).replace "\n" "\n  "
    s!"declare({name}, {init},\n  {str_body}\n)"
  | .assign_var lv _ v _ _ body =>
    s!"{lv} = {v}\n{Stmt.listToString body}"
  | .assign lv _ v _  => s!"{lv} = {v}"
  | .asnop lv op v  => s!"{lv} {op}= {v}"
  | .ite cond tt ff =>
    let str_tt := (Stmt.listToString tt).replace "\n" "\n  "
    let str_ff := (Stmt.listToString ff).replace "\n" "\n  "
    s!"if{cond}\n  {str_tt}\nelse\n  {str_ff}\nendif"
  | .while cond annos body =>
    let str_annos := Anno.listToString (annos.map (·.val))
    let str_body := (Stmt.listToString body).replace "\n" "\n  "
    s!"while{cond}\n  {str_annos}{str_body}\nendwhile"
  | .return_void  => s!"return"
  | .return_tau e => s!"return {e}"
  | .assert e     => s!"assert{e}"
  | .error e      => s!"error{e}"
  | .expr e       => s!"{e}"
  | .anno a       => Anno.toString a.val

partial def Stmt.listToString : Stmt.List Δ Γ ρ → String
  | .nil => "nop;"
  | .cons stmt .nil => s!"{Stmt.toString stmt};"
  | .cons stmt stmts =>
    s!"{Stmt.toString stmt};\n{Stmt.listToString stmts}"
end

instance : ToString (Stmt Δ Γ ρ)      := ⟨Stmt.toString⟩
instance : ToString (Stmt.List Δ Γ ρ) := ⟨Stmt.listToString⟩


instance : ToString SDef where
  toString s :=
    s!"struct {s.name}".append ("{".append ( s!"{s.fields}".append "};"))

instance : ToString (FDecl Δ) where toString f :=
  s!"{f.ret} {f.name}({f.params})\n  {toString f.annos}"
instance : ToString (FDef Δ) where
  toString f :=
    let str_anno := toString f.annos
    let str_body := (toString f.body).replace "\n" "\n  "
    s!"{f.ret} {f.name}({f.params})\n  {str_anno}{str_body}\nend {f.name}"

def GDecl.toString : (GDecl Δ Δ') → String
  | .fdecl f => s!"{f}"
  | .fdef  f => s!"{f}"
  | .sdef  s => s!"{s}"
instance : ToString (GDecl Δ Δ') where toString := GDecl.toString

def GDecl.List.toStrings : GDecl.List Δ Δ' → _root_.List String
  | .nil => []
  | .cons gs g => g.toString :: gs.toStrings
  | .update gs => gs.toStrings

instance : ToString Prog where
  toString prog :=
    let calls_str  := prog.calls.toList.map (fun (f, pure) =>
        if pure then s!"{f} (pure)" else s!"{f}")
      |> String.intercalate "\n  "
    let string_str := prog.strings.map (·.replace "\n" "\n    ")
      |> String.intercalate "\n  - "
    let prog_str := prog.header.toStrings ++ prog.body.toStrings
      |> "\n\n".intercalate
    s!"-----  Calls  -----\n  {calls_str}\n
----- Strings -----\n  - {string_str}\n
----- Program -----\n\n{prog_str}\n
----- ------- -----\n"
