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

structure FuncSig where
  arity  : Nat
  argTys : Fin arity → Typ
  retTy  : Typ    -- use .any if void

structure Status.Func where
  type    : FuncSig
  defined : Bool

structure Status.Struct where
  fields  : Symbol → Option Typ
  defined : Bool

inductive Status.Symbol
| var   (v : Typ)
| func  (f : Status.Func)
| alias (t : Typ)

-- use Status.Symbol to prevent collisions with funcs/tydefs
abbrev FCtx := Symbol → Option Status.Symbol

@[inline] def FCtx.update (Γ : FCtx) (x : Symbol) (s : Status.Symbol) : FCtx :=
  Function.update Γ x (some s)
@[inline] def FCtx.updateVar (Γ : FCtx) (x : Symbol) (τ : Typ) : FCtx :=
  Γ.update x (.var τ)
@[inline] def FCtx.updateFunc
    (Γ : FCtx) (x : Symbol) (s : Status.Func) : FCtx :=
  Γ.update x (.func s)
@[inline] def FCtx.ofParams (params : List (Typed Symbol)) : FCtx :=
  (params.map (fun p => (p.data, .var p.type))).toMap
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

structure GCtx where
  symbols : Symbol → Option Status.Symbol := fun _ => none
  struct  : Symbol → Option Status.Struct := fun _ => none
deriving Inhabited

@[inline] def FCtx.init
    (Δ : GCtx) (params : List (Typed Symbol)) : FCtx :=
  let params_Γ := FCtx.ofParams params
  fun x =>
    match params_Γ x with
    | some status => some status
    | none => Δ.symbols x

/- TST expressions are similar to the AST expressions but they are also encoded
   with type information such that an ill-typed TST-expression cannot be
   constructed. Another way of thinking about it is that these are both a
   representation of the language and the static rules themselves.

   One difference from the traditional static semantic rules is that we use
   "Fording" in some places. A traditional rule would specify that would have
   some type (e.g. `binop_int : int → int → int`). In our case this can cause
   problems when generating the TST and proving properties about it. So instead
   we allow sub-expressions to be any type, and then later require a proof that
   they are equal/equivalent to the required type (e.g.
   `binop_int : τ₁ → τ₁ = int → τ₂ → τ₂ = int → int`). We are allowing any type,
   so long as it's the correct one ("Any color [...], so long as it's black").
 -/
open Typ.Notation in
inductive Expr (Δ : GCtx) (Γ : FCtx) : (τ : Typ) → Type
| num  : Int32  → Expr Δ Γ (int)
| char : Char   → Expr Δ Γ (char)
| str  : String → Expr Δ Γ (string)
| var
  : {τ : Typ}
  → (x : Symbol)
  → Γ x = .some (.var τ)
  → Expr Δ Γ τ
| «true»  : Expr Δ Γ (bool)
| «false» : Expr Δ Γ (bool)
| null    : Expr Δ Γ (any *)
| unop
  : (op : UnOp)
  → τ.equiv op.type
  → (e : Expr Δ Γ τ)
  → Expr Δ Γ op.type
| binop_int
  : {τ₁ : {τ : Typ // τ = (int)}}
  → {τ₂ : {τ : Typ // τ = (int)}}
  → (op : BinOp.Int)
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ (int)
| binop_bool
  : {τ₁ : {τ : Typ // τ = (bool)}}
  → {τ₂ : {τ : Typ // τ = (bool)}}
  → (op : BinOp.Bool)
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ (bool)
| binop_eq
  : (op : Comparator)
  → op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → τ₁.equiv τ₂
  → τ₁.is_eqtype ∨ τ₂.is_eqtype
  → Expr Δ Γ (bool)
| binop_rel₁
  : {τ₁ : {τ : Typ // τ = (int)}}
  → {τ₂ : {τ : Typ // τ = (int)}}
  → (op : Comparator)
  → ¬op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ (bool)
| binop_rel₂
  : {τ₁ : {τ : Typ // τ = (char)}}
  → {τ₂ : {τ : Typ // τ = (char)}}
  → (op : Comparator)
  → ¬op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ (bool)
| ternop
  : {τ₁ : {τ : Typ // τ = (bool)}}
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
| alloc : (τ : Typ) → Expr Δ Γ (τ*)
| alloc_array
  : {τ₁ : {τ : Typ // τ = (int)}}
  → (τ : Typ)
  → Expr Δ Γ τ₁
  → Expr Δ Γ (τ[])
| dot
  : {τ₁ : {τ : Typ // τ = (struct s)}}
  → Expr Δ Γ τ₁
  → (field : Symbol)
  → Δ.struct s = .some ⟨struct_fields, true⟩
  → struct_fields field = .some τ
  → Expr Δ Γ τ
| deref
  : {τ₁ : {τ' : Typ // τ' = (τ*)}}
  → Expr Δ Γ τ₁
  → Expr Δ Γ τ
| index
  : {τ₁ : {τ' : Typ // τ' = (τ[])}}
  → {τ₂ : {τ : Typ // τ = (int)}}
  → Expr Δ Γ τ₁
  → Expr Δ Γ τ₂
  → Expr Δ Γ τ
| result : Expr Δ Γ τ
| length
  : {τ₁ : {τ' : Typ // τ' = (τ[])}}
  → Expr Δ Γ τ₁
  → Expr Δ Γ (int)

namespace Expr
open Typ.Notation

@[inline] def typeWith {p : Typ → Prop} (e : Expr Δ Γ τ) (h : p τ)
    : Expr Δ Γ (⟨τ, h⟩ : {τ : Typ // p τ}) := e
@[inline] def typeWithEq {τ₂ : Typ} (e : Expr Δ Γ τ) (eq : τ = τ₂)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = τ₂}) :=
  e.typeWith (p := fun t => t = τ₂) eq
@[inline] def typeWithEquiv {τ₂ : Typ} (e : Expr Δ Γ τ) (eq : τ.equiv τ₂)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ.equiv τ₂}) :=
  e.typeWith (p := fun t => t.equiv τ₂) eq


@[inline] def intType (e : Expr Δ Γ τ) (eq : τ = (int))
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (int)}) := e.typeWithEq eq
@[inline] def boolType (e : Expr Δ Γ τ) (eq : τ = (bool))
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (bool)}) := e.typeWithEq eq
@[inline] def charType (e : Expr Δ Γ τ) (eq : τ = .prim .char)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = .prim .char}) := e.typeWithEq eq
@[inline] def stringType (e : Expr Δ Γ τ) (eq : τ = .prim .string)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = .prim .string}) := e.typeWithEq eq
@[inline] def ptrType (e : Expr Δ Γ τ) (τ' : Typ) (eq : τ = (τ'*))
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (τ'*)}) := e.typeWithEq eq
@[inline] def arrType (e : Expr Δ Γ τ) (τ' : Typ) (eq : τ = (τ'[]))
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (τ'[])}) := e.typeWithEq eq
@[inline] def structType (e : Expr Δ Γ τ) (s : Symbol) (eq : τ = (struct s))
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (struct s)}) := e.typeWithEq eq

/- Assert that P can be folded to some value through every sub-expression -/
inductive Fold {Δ : GCtx} {Γ : FCtx}
    : (P : (τ : Typ) → α → Expr Δ Γ τ → Option α)
    → α → Expr Δ Γ τ → α → Prop
| num
  : {a₁ a₂ : α}
  → P _ a₁ (.num v) = some a₂
  → Fold P a₁ ((.num v) : Expr Δ Γ _) a₂
| char
  : {a₁ a₂ : α}
  → P _ a₁ (.char c) = some a₂
  → Fold P a₁ ((.char c) : Expr Δ Γ _) a₂
| str
  : {a₁ a₂ : α}
  → P _ a₁ (.str s) = some a₂
  → Fold P a₁ ((.str s) : Expr Δ Γ _) a₂
| var
  : {a₁ a₂ : α}
  → {h : Γ x = .some (.var τ)}
  → P _ a₁ (.var x h) = some a₂
  → Fold P a₁ ((.var x h) : Expr Δ Γ _) a₂
| «true»
  : {a₁ a₂ : α}
  → P _ a₁ .true = some a₂
  → Fold P a₁ (.true : Expr Δ Γ _) a₂
| «false»
  : {a₁ a₂ : α}
  → P _ a₁ .false = some a₂
  → Fold P a₁ (.false : Expr Δ Γ _) a₂
| null
  : {a₁ a₂ : α}
  → P _ a₁ .null = some a₂
  → Fold P a₁ (.null : Expr Δ Γ _) a₂
| unop
  : {a₁ a₂ a₃ : α}
  → Fold P a₁ e a₂
  → P _ a₂ (.unop op eq e) = some a₃
  → Fold P a₁ (.unop op eq e) a₃
| binop_int
  : {a₁ a₂ a₃ a₄ : α}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_int op l r) = some a₄
  → Fold P a₁ (.binop_int op l r) a₄
| binop_bool
  : {a₁ a₂ a₃ a₄ : α}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_bool op l r) = some a₄
  → Fold P a₁ (.binop_bool op l r) a₄
| binop_eq
  : {a₁ a₂ a₃ a₄ : α}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_eq op eq l r h₁ h₂) = some a₄
  → Fold P a₁ (.binop_eq op eq l r h₁ h₂) a₄
| binop_rel₁
  : {a₁ a₂ a₃ a₄ : α}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_rel₁ op eq l r) = some a₄
  → Fold P a₁ (.binop_rel₁ op eq l r) a₄
| binop_rel₂
  : {a₁ a₂ a₃ a₄ : α}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_rel₂ op eq l r) = some a₄
  → Fold P a₁ (.binop_rel₂ op eq l r) a₄
| ternop
  : {a₁ a₂ a₃ a₄ a₅ : α}
  → Fold P a₁ cc a₂
  → Fold P a₂ tt a₃
  → Fold P a₃ ff a₄
  → P _ a₄ (.ternop cc tt ff h₂) = some a₅
  → Fold P a₁ (.ternop cc tt ff h₂) a₅
| app
  : {a₁ a₂ a₃ : α}
  → {hsig : Γ f = .some (.func status)}
  → {τs : Fin (status.type.arity) → Typ}
  → {eq : ∀ i, (status.type.argTys i).equiv (τs i)}
  → {args : (i : Fin status.type.arity) → Expr Δ Γ (τs i)}
  → (∀ i : Fin status.type.arity, -- nb not sequential nor joins
      Fold P a₁ (args i) a₂ )
  → P _ a₂ (.app f hsig τs eq args) = some a₃
  → Fold P a₁ (.app f hsig τs eq args) a₃
| alloc
  : {a₁ a₂ : α}
  → P _ a₁ (.alloc τ₁) = some a₂
  → Fold P a₁ (.alloc τ₁) a₂
| alloc_array
  : {a₁ a₂ a₃ : α}
  → Fold P a₁ e a₂
  → P _ a₂ (.alloc_array τ₁ e) = some a₃
  → Fold P a₁ (.alloc_array τ₁ e) a₃
| dot
  : {a₁ a₂ a₃ : α}
  → Fold P a₁ e a₂
  → P _ a₂ (.dot e f h₁ h₂) = some a₃
  → Fold P a₁ (.dot e f h₁ h₂) a₃
| deref
  : {a₁ a₂ a₃ : α}
  → Fold P a₁ e a₂
  → P _ a₂ (.deref e) = some a₃
  → Fold P a₁ (.deref e) a₃
| index
  : {a₁ a₂ a₃ : α}
  → Fold P a₁ e a₂
  → Fold P a₂ indx a₃
  → P _ a₃ (.index e indx) = some a₄
  → Fold P a₁ (.index e indx) a₄
| result
  : {a₁ a₂ : α}
  → P (τ := τ) a₁ .result = some a₂
  → Fold P a₁ (.result : Expr Δ Γ τ) a₂
| length
  : {a₁ a₂ a₃ : α}
  → Fold P a₁ e a₂
  → P _ a₂ (.length e) = some a₃
  → Fold P a₁ (.length e) a₃

def All (P : {τ : Typ} → Expr Δ Γ τ → Bool) (e : Expr Δ Γ τ) : Prop :=
  Expr.Fold (fun _ _ e => if P e then some () else none) () e ()

@[inline] def only_contract : Expr Δ Γ τ → Bool
  | .result   => .true
  | .length _ => .true
  | _         => .false
@[inline] def has_result : Expr Δ Γ τ → Bool
  | .result => .true
  | _       => .false

@[inline] def no_contract : Expr Δ Γ τ → Bool :=
  .not ∘ only_contract
@[inline] def no_result   : Expr Δ Γ τ → Bool :=
  .not ∘ has_result

abbrev NoContract Δ Γ τ := {e : Expr Δ Γ τ // All no_contract e}
abbrev NoResult   Δ Γ τ := {e : Expr Δ Γ τ // All no_result   e}

end Expr

open Typ.Notation in
inductive LValue (Δ : GCtx) (Γ : FCtx) : Typ → Type
| var   : (x : Symbol)
        → (Γ x = .some (.var τ))
        → LValue Δ Γ τ
| dot   : {τ₁ : {τ : Typ // τ = (struct s)}}
        → LValue Δ Γ τ₁
        → (field : Symbol)
        → Δ.struct s = .some ⟨fields, true⟩
        → fields field = .some τ
        → LValue Δ Γ τ
| deref : {τ₁ : {τ' : Typ // τ' = (τ*)}}
        → LValue Δ Γ τ₁
        → LValue Δ Γ τ
| index : {τ₁ : {τ' : Typ // τ' = (τ[])}}
        → {τ₂ : {τ : Typ // τ = (int)}}
        → LValue Δ Γ τ₁
        → Expr.NoContract Δ Γ τ₂
        → LValue Δ Γ τ

namespace LValue

open Typ.Notation

@[inline] def is_var : LValue Δ Γ τ → Bool
  | .var _ _ => true | _ => false
@[inline] def get_name
    (lval : LValue Δ Γ τ) (h₁ : lval.is_var) : Symbol :=
  match h₂ : lval with
  | .var name _   => name
  | .dot _ _ _ _
  | .deref _
  | .index _ _    => by simp [is_var] at h₁

@[inline] def typeWith {p : Typ → Prop} (e : LValue Δ Γ τ) (h : p τ)
    : LValue Δ Γ (⟨τ, h⟩ : {τ : Typ // p τ}) := e
@[inline] def typeWithEq {τ₂ : Typ} (e : LValue Δ Γ τ) (eq : τ = τ₂)
    : LValue Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = τ₂}) :=
  e.typeWith (p := fun t => t = τ₂) eq

@[inline] def intType (e : LValue Δ Γ τ) (eq : τ = (int))
    : LValue Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (int)}) := e.typeWithEq eq
@[inline] def ptrType (e : LValue Δ Γ τ) (τ' : Typ) (eq : τ = (τ'*))
    : LValue Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (τ'*)}) := e.typeWithEq eq
@[inline] def arrType (e : LValue Δ Γ τ) (τ' : Typ) (eq : τ = (τ'[]))
    : LValue Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (τ'[])}) := e.typeWithEq eq
@[inline] def structType (e : LValue Δ Γ τ) (s : Symbol) (eq : τ = (struct s))
    : LValue Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (struct s)}) := e.typeWithEq eq

structure Predicate (Δ : GCtx) (Γ : FCtx) (α : Type) where
  lval : (τ : Typ) → α → LValue Δ Γ τ → Option α
  expr : (τ : Typ) → α → Expr Δ Γ τ → Option α

/- Assert that some predicate P applies to every sub-lvalue -/
inductive Fold : {Δ : GCtx} → {Γ : FCtx}
  → (P : LValue.Predicate Δ Γ α) → α → LValue Δ Γ τ → α → Prop
| var
  : {a₁ a₂ : α}
  → {P : LValue.Predicate Δ Γ α}
  -- → {τ₁ : {τ' : Typ // τ' = τ}}
  → {h : Γ x = .some (.var τ)}
  → P.lval _ a₁ (.var x h) = some a₂
  → Fold P a₁ ((.var x h) : LValue Δ Γ _) a₂
| dot
  : Fold P a₁ l a₂
  → P.lval _ a₂ (.dot l f h₁ h₂) = some a₃
  → Fold P a₁ (.dot l f h₁ h₂) a₃
| deref
  : Fold P a₁ l a₂
  → P.lval _ a₂ (.deref l) = some a₃
  → Fold P a₁ (.deref l) a₃
| index
  : Fold P a₁ l a₂
  → Expr.Fold P.expr a₂ e.val a₃
  → P.lval _ a₃ (.index l e) = some a₄
  → Fold P a₁ (.index l e) a₄

end LValue

open Typ.Notation in
inductive Anno (Δ : GCtx) (Γ : FCtx) : Type
| requires   : {τ : {τ : Typ // τ = (bool)}} → Expr.NoResult Δ Γ τ → Anno Δ Γ
| ensures    : {τ : {τ : Typ // τ = (bool)}} → Expr          Δ Γ τ → Anno Δ Γ
| loop_invar : {τ : {τ : Typ // τ = (bool)}} → Expr.NoResult Δ Γ τ → Anno Δ Γ
| assert     : {τ : {τ : Typ // τ = (bool)}} → Expr.NoResult Δ Γ τ → Anno Δ Γ

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

-- todo should we check annotation too? is that useful?
open Typ.Notation in
inductive Anno.Fold
    : (P : (τ : Typ) → α → Expr Δ Γ τ → Option α)
    → α → Anno Δ Γ → α → Prop
| requires
  : {a₁ a₂ : α}
  → {τ : {τ : Typ // τ = (bool)}}
  → {e : Expr.NoResult Δ Γ τ}
  → Expr.Fold P a₁ e.val a₂
  → Anno.Fold P a₁ (.requires e) a₂
| ensures
  : {a₁ a₂ : α}
  → {τ : {τ : Typ // τ = (bool)}}
  → {e : Expr Δ Γ τ}
  → Expr.Fold P a₁ e a₂
  → Anno.Fold P a₁ (.ensures e) a₂
| loop_invar
  : {a₁ a₂ : α}
  → {τ : {τ : Typ // τ = (bool)}}
  → {e : Expr.NoResult Δ Γ τ}
  → Expr.Fold P a₁ e.val a₂
  → Anno.Fold P a₁ (.loop_invar e) a₂
| assert
  : {a₁ a₂ : α}
  → {τ : {τ : Typ // τ = (bool)}}
  → {e : Expr.NoResult Δ Γ τ}
  → Expr.Fold P a₁ e.val a₂
  → Anno.Fold P a₁ (.assert e) a₂

inductive Anno.List.Fold
    : (P : (τ : Typ) → α → Expr Δ Γ τ → Option α)
    → α → List (Anno Δ Γ) → α → Prop
| nil : Anno.List.Fold P a [] a
| cons
  : Anno.Fold P a₁ anno a₂
  → Anno.List.Fold P a₂ annos a₃
  → Anno.List.Fold P a₁ (anno :: annos) a₃

open Typ.Notation in
mutual
inductive Stmt (Δ : GCtx) : (Γ : FCtx) → Option Typ → Type
| decl
  : (name : Typed Symbol)
  → (new_ctx : Γ' = Γ.updateVar name.data name.type)
  → (body : Stmt.List Δ Γ' ρ)
  → Stmt Δ Γ ρ
| decl_init
  : (name : Typed Symbol)
  → (init : Expr.NoContract Δ Γ τ)
  → (ty_equiv : name.type.equiv τ)
  → (new_ctx : Γ' = Γ.updateVar name.data name.type)
  → (body : Stmt.List Δ Γ' ρ)
  → Stmt Δ Γ ρ
| assign_var
  : (lhs : LValue Δ Γ τ₁)
  → (is_var : lhs.is_var)
  → (rhs : Expr.NoContract Δ Γ τ₂)
  → (ty_equiv : τ₁.equiv τ₂)
  → Stmt Δ Γ ρ
| assign
  : (lhs : LValue Δ Γ τ₁)
  → (is_var : ¬lhs.is_var)
  → (rhs : Expr.NoContract Δ Γ τ₂)
  → (ty_equiv : τ₁.equiv τ₂)
  → Stmt Δ Γ ρ
| asnop
  : {τ₁ : {τ : Typ // τ = .prim .int}}
  → {τ₂ : {τ : Typ // τ = .prim .int}}
  → (lhs : LValue Δ Γ τ₁)
  → BinOp.Int
  → (rhs : Expr.NoContract Δ Γ τ₂)
  → Stmt Δ Γ ρ
| expr
  : Expr.NoContract Δ Γ τ
  → Stmt Δ Γ ρ
| ite
  : {τ : {τ : Typ // τ = (bool)}}
  → (cond : Expr.NoContract Δ Γ τ)
  → (tt : Stmt.List Δ Γ ρ)
  → (ff : Stmt.List Δ Γ ρ)
  → Stmt Δ Γ ρ
| while
  : {τ : {τ : Typ // τ = (bool)}}
  → (cond : Expr.NoContract Δ Γ τ)
  → List (Anno.Loop Δ Γ)
  → Stmt.List Δ Γ ρ
  → Stmt Δ Γ ρ
| return_void
  : (is_void : ρ.isNone)
  → Stmt Δ Γ ρ
| return_tau
  : {τ₁ : {τ' : Typ // τ' = τ }}
  → Expr.NoContract Δ Γ τ₁
  → Stmt Δ Γ (some τ)
| assert
  : {τ : {τ : Typ // τ = (bool)}}
  → Expr.NoContract Δ Γ τ
  → Stmt Δ Γ ρ
| error
  : {τ : {τ : Typ // τ = (string)}}
  → Expr.NoContract Δ Γ τ
  → Stmt Δ Γ ρ
| anno : Anno.Free Δ Γ → Stmt Δ Γ ρ

inductive Stmt.List (Δ : GCtx) : (Γ : FCtx) → Option Typ → Type
| nil  : Stmt.List Δ Γ ρ
| cons : (s : Stmt Δ Γ ρ) → Stmt.List Δ Γ ρ → Stmt.List Δ Γ ρ
end

def Stmt.List.consEnd : Stmt.List Δ Γ ρ → Stmt Δ Γ ρ → Stmt.List Δ Γ ρ
  | .nil, s => .cons s .nil
  | .cons x xs, s => .cons x (consEnd xs s)

def Stmt.List.toList : Stmt.List Δ Γ ρ → _root_.List (Stmt Δ Γ ρ)
  | .nil => .nil
  | .cons stmt stmts => stmt :: toList stmts

def Stmt.List.ofList : _root_.List (Stmt Δ Γ ρ) → Stmt.List Δ Γ ρ
  | .nil => .nil
  | stmt :: stmts => cons stmt (ofList stmts)

instance : Coe (Stmt.List Δ Γ ρ) (List (Stmt Δ Γ ρ)) := ⟨Stmt.List.toList⟩

/- When "folding" over statements we want to be able to first update the
      accumulator based on the statement then fold over body. This means we
      need to be able to see the high-level structure of the statement before
      actually checking. This is what the `Stmt.Peek` inductive is for.

  If you have/know a better solution feel free to let me know : )
  In general I'm not confident that these are the "right" definitions (for both
  `Peek` and `Fold`) but I'm going to go with it.

  Tbh just being able to derive this from the `Stmt` type would be cool if
  possible.
 -/
inductive Stmt.Peek (Δ : GCtx) (Γ : FCtx)
| decl (name : Typed Symbol)
| decl_init (name : Typed Symbol) (init : Expr.NoContract Δ Γ τ)
| assign_var (lhs : LValue Δ Γ τ₁)
             (is_var : lhs.is_var)
             (rhs : Expr.NoContract Δ Γ τ₂)
| assign (lhs : LValue Δ Γ τ₁)
         (is_var : ¬lhs.is_var)
         (rhs : Expr.NoContract Δ Γ τ₂)
| asnop (lhs : LValue Δ Γ τ₁)
        (op : BinOp.Int)
        (rhs : Expr.NoContract Δ Γ τ₂)
| expr (e : Expr.NoContract Δ Γ τ)
| ite (cond : Expr.NoContract Δ Γ τ)
| while (cond : Expr.NoContract Δ Γ τ) -- should have annos?
| return_void
| return_tau (e : Expr.NoContract Δ Γ τ)
| assert (e : Expr.NoContract Δ Γ τ)
| error (e : Expr.NoContract Δ Γ τ)
| anno

structure Stmt.Predicate (Δ : GCtx) (Γ : FCtx) (α : Type) where
  init : α → Stmt.Peek Δ Γ → Option α
  stmt : {ρ : Option Typ} → α → Stmt Δ Γ ρ → Option α
  lval : (τ : Typ) → α → LValue Δ Γ τ → Option α
  expr : (τ : Typ) → α → Expr Δ Γ τ → Option α
  join : α → α → Stmt Δ Γ ρ → Option α -- should join use the Peek?

@[simp] def Stmt.Predicate.toLValuePred (P : Stmt.Predicate Δ Γ α)
    : LValue.Predicate Δ Γ α := ⟨P.lval, P.expr⟩

open Typ.Notation in
mutual
inductive Stmt.Fold
    : {Δ : GCtx} → {Γ : FCtx}
    → (P : {Γ : FCtx} → Stmt.Predicate Δ Γ α) → (a : α) → Stmt Δ Γ ρ → α → Prop
| decl
  : {a₁ a₂ a₃ a₄ : α}
  → {h : Γ' = Γ.updateVar name.data name.type}
  → {body : Stmt.List Δ Γ' ρ}
  → P.init (Γ := Γ) a₁ (.decl name) = some a₂
  → Stmt.List.Fold (Γ := Γ') P a₂ body a₃
  → P.join a₂ a₃ (.decl name h body) = some a₄
  → Stmt.Fold P a₁ ((.decl name h body) : Stmt Δ Γ ρ) a₄
| decl_init
  : {a₁ a₂ a₃ a₄ a₅ : α}
  → {init : Expr.NoContract Δ Γ τ}
  → {body : Stmt.List Δ Γ' ρ}
  → Expr.Fold P.expr a₂ init.val a₂
  → P.init (Γ := Γ) a₂ (.decl_init name init) = some a₃
  → Stmt.List.Fold (Γ := Γ') P a₃ body a₄
  → P.join a₃ a₄ (.decl_init name init eq h body) = some a₅
  → Stmt.Fold P a₁ (.decl_init name init eq h body) a₅
| assign_var
  : {lhs : LValue Δ Γ τ₁}
  → {rhs : Expr.NoContract Δ Γ τ₂}
  → {var : lhs.is_var}
  → {a₁ a₂ a₃ a₄ : α}
  → Expr.Fold P.expr a₁ rhs.val a₂
  → P.init (Γ := Γ) a₂ (.assign_var lhs var rhs) = some a₃
  → P.stmt (ρ := ρ) a₃ (.assign_var lhs var rhs eq) = some a₄
  → Stmt.Fold P a₁ ((.assign_var lhs var rhs eq) : Stmt Δ Γ ρ) a₄
| assign
  : {lhs : LValue Δ Γ τ₁}
  → {rhs : Expr.NoContract Δ Γ τ₂}
  → {var : ¬lhs.is_var}
  → {a₁ a₂ a₃ a₄ a₅ : α}
  → LValue.Fold P.toLValuePred a₁ lhs a₂
  → P.init (Γ := Γ) a₂ (.assign lhs var rhs) = some a₃
  → Expr.Fold P.expr a₃ rhs.val a₄
  → P.stmt (ρ := ρ) a₄ (.assign lhs var rhs eq) = some a₅
  → Stmt.Fold P a₁ ((.assign lhs var rhs eq) : Stmt Δ Γ ρ) a₅
| asnop
  : {τ₁ τ₂ : {τ : Typ // τ = (int)}}
  → {lhs : LValue Δ Γ τ₁}
  → {rhs : Expr.NoContract Δ Γ τ₂}
  → {a₁ a₂ a₃ a₄ a₅ : α}
  → P.init (Γ := Γ) a₁ (.asnop lhs op rhs) = some a₂
  → LValue.Fold P.toLValuePred a₂ lhs a₃
  → Expr.Fold P.expr a₃ rhs.val a₄
  → P.stmt (ρ := ρ) a₄ (.asnop lhs op rhs) = some a₅
  → Stmt.Fold P a₁ ((.asnop lhs op rhs) : Stmt Δ Γ ρ) a₅
| expr
  : {e : Expr.NoContract Δ Γ τ}
  → {a₁ a₂ a₃ a₄ : α}
  → P.init (Γ := Γ) a₁ (.expr e) = some a₂
  → Expr.Fold P.expr a₂ e.val a₃
  → P.stmt (ρ := ρ) a₃ (.expr e) = some a₄
  → Stmt.Fold P a₁ ((.expr e) : Stmt Δ Γ ρ) a₄
| ite
  : {τ : {τ : Typ // τ = (bool)}}
  → {cond : Expr.NoContract Δ Γ τ}
  → {tt ff : Stmt.List Δ Γ ρ}
  → {a₁ a₂ a_t a_f : α}
  → Expr.Fold P.expr a₁ cond.val a₂
  → P.init (Γ := Γ) a₂ (.ite cond) = some a₃
  → Stmt.List.Fold P a₃ tt a_t
  → Stmt.List.Fold P a₃ ff a_f
  → P.join a_t a_f (.ite cond tt ff) = some a₄
  → Stmt.Fold P a₁ (.ite cond tt ff) a₄
| while
  : {τ : {τ : Typ // τ = (bool)}}
  → {cond : Expr.NoContract Δ Γ τ}
  → {body : Stmt.List Δ Γ ρ}
  → {a₁ a₂ a₃ a₄ a₅ a₆ : α}
  → Expr.Fold P.expr a₁ cond.val a₂
  → Anno.List.Fold P.expr a₂ (annos.map (·.val)) a₃
  → P.init (Γ := Γ) a₃ (.while cond) = some a₄
  → Stmt.List.Fold P a₄ body a₅
  → P.join a₂ a₅ (.while cond annos body) = some a₆
  → Stmt.Fold P a₁ (.while cond annos body) a₆
| return_void
  : {a₁ a₂ : α}
  → {ρ : Option Typ}
  → {h : ρ.isNone}
  → {P : {Γ : FCtx} → Stmt.Predicate Δ Γ α}
  → P.stmt (Γ := Γ) a₁ (.return_void h) = some a₂
  → Stmt.Fold P a₁ ((.return_void h) : Stmt Δ Γ ρ) a₂
| return_tau
  : {τ₁ : {τ' : Typ // τ' = τ}}
  → {e : Expr.NoContract Δ Γ τ₁}
  → {a₁ a₂ a₃ a₄ : α}
  → P.init (Γ := Γ) a₁ (.return_tau e) = some a₂
  → Expr.Fold P.expr a₂ e.val a₃
  → P.stmt a₃ (.return_tau e) = some a₄
  → Stmt.Fold P a₁ (.return_tau e) a₄
| assert
  : {τ : {τ : Typ // τ = (bool)}}
  → {e : Expr.NoContract Δ Γ τ}
  → {a₁ a₂ a₃ a₄ : α}
  → P.init (Γ := Γ) a₁ (.assert e) = some a₂
  → Expr.Fold P.expr a₂ e.val a₃
  → P.stmt a₃ ((.assert e) : Stmt Δ Γ ρ) = some a₄
  → Stmt.Fold P a₁ ((.assert e) : Stmt Δ Γ ρ) a₄
| error
  : {τ : {τ : Typ // τ = (string)}}
  → {e : Expr.NoContract Δ Γ τ}
  → {a₁ a₂ a₃ a₄ : α}
  → P.init (Γ := Γ) a₁ (.error e) = some a₂
  → Expr.Fold P.expr a₂ e.val a₃
  → P.stmt a₃ ((.error e) : Stmt Δ Γ ρ) = some a₄
  → Stmt.Fold P a₁ ((.error e) : Stmt Δ Γ ρ) a₄
| anno
  : {an : Anno.Free Δ Γ}
  → {a₁ a₂ a₃ a₄ : α}
  → P.init (Γ := Γ) a₁ .anno = some a₂
  → Anno.Fold P.expr a₂ an.val a₃
  → P.stmt a₃ ((.anno an) : Stmt Δ Γ ρ) = some a₄
  → Stmt.Fold P a₁ ((.anno an) : Stmt Δ Γ ρ) a₄

inductive Stmt.List.Fold
    : {Δ : GCtx} → {Γ : FCtx}
    → (P : {Γ : FCtx} → Stmt.Predicate Δ Γ α)
    → (a : α) → Stmt.List Δ Γ ρ → α → Prop
| nil  : Stmt.List.Fold P a .nil a
| cons : Stmt.Fold P a₁ stmt a₂
       → Stmt.List.Fold P a₂ stmts a₃
       → Stmt.List.Fold P a₁ (.cons stmt stmts) a₃
end

theorem Stmt.List.Fold.consEnd
    {a₁ a₂ a₃ : α}
    {stmt : Stmt Δ Γ ρ}
    (stmts : Stmt.List Δ Γ ρ)
    (hstmts : Stmt.List.Fold P a₁ stmts a₂)
    (hstmt : Stmt.Fold P a₂ stmt a₃)
    : Stmt.List.Fold P a₁ (stmts.consEnd stmt) a₃ := by
  cases h : stmts with
  | nil =>
    simp [Stmt.List.consEnd]
    cases hstmts with
    | nil => exact .cons hstmt .nil
    | cons _ _ => contradiction
  | cons x xs =>
    simp [Stmt.List.consEnd]
    cases hstmts with
    | nil => contradiction
    | cons hx hxs => next x' xs' =>
      have : sizeOf xs < sizeOf (List.cons x xs) := by simp
      simp [Stmt.List.cons.inj h] at hx hxs
      exact .cons hx (Fold.consEnd xs hxs hstmt)


/- Used for verifying that all variables are initialised when used -/
abbrev Initialised.Acc := Symbol → Bool
def Initialised.Acc.empty : Acc := fun _ => false
def Initialised.Acc.ofList : List Symbol → Acc :=
  fun lst => fun x => x ∈ lst

@[simp] def Initialised.init (acc : Acc) : Stmt.Peek Δ Γ → Acc
  | .decl_init name _ =>
    (fun x => if x = name.data then true else acc x)
  | .assign_var lv h _ =>
    let name := LValue.get_name lv h
    (fun x => if x = name then true else acc x)
  | _ => acc

@[simp] def Initialised.stmt (acc : Acc) : Stmt Δ Γ ρ → Acc
  | .return_tau _
  | .return_void _     -- end of controlflow initialises all decl'd variables
  | .error _        => fun x => if let some _ := Γ x then true else false
  | _ => acc

@[simp] def Initialised.lval (τ : Typ) (acc : Acc) : LValue Δ Γ τ → Option Acc
  | .var x _ => if acc x then some acc else none
  | _        => some acc

@[simp] def Initialised.expr (τ : Typ) (acc : Acc) : Expr Δ Γ τ → Option Acc
  | .var x _ => if acc x then some acc else none
  | _        => some acc

@[simp] def Initialised.join (acc₁ acc₂ : Acc) : Stmt Δ Γ ρ → Acc
  | .while _ _ _ => acc₁
  | .decl_init name _ _ _ _
  | .decl name _ _  => (fun x => if x = name.data then false else acc₂ x)
  | _ => (fun x => acc₁ x && acc₂ x)

@[simp] def Initialised.Predicate : Stmt.Predicate Δ Γ Acc :=
  { init := fun acc s => some (init acc s)
  , stmt := fun acc s => some (stmt acc s)
  , lval
  , expr
  , join := fun acc₁ acc₂ s => some (join acc₁ acc₂ s)
  }

@[simp] def Initialised.Expr (expr : Tst.Expr Δ Γ τ) inits :=
  Expr.Fold Initialised.expr inits expr inits
@[simp] def Initialised.LValue (lv : Tst.LValue Δ Γ τ) inits :=
  LValue.Fold Initialised.Predicate.toLValuePred inits lv inits
@[simp] def Initialised.Anno (anno : Tst.Anno Δ Γ) inits :=
  Anno.Fold Initialised.expr inits anno inits
@[simp] def Initialised.Anno.List (annos : List (Tst.Anno Δ Γ)) inits :=
  Anno.List.Fold Initialised.expr inits annos inits

@[simp] def Initialised.Stmt (stmt : Tst.Stmt Δ Γ ρ) inits inits' :=
  Stmt.Fold Initialised.Predicate inits stmt inits'
@[simp] def Initialised.Stmt.List (stmt : Tst.Stmt.List Δ Γ ρ) inits inits' :=
  Stmt.List.Fold Initialised.Predicate inits stmt inits'


/- Used for verifying that all control flow paths return -/
@[simp] def Returns.init (acc : Bool) : Stmt.Peek Δ Γ → Bool
  | _ => acc
@[simp] def Returns.stmt (acc : Bool) : Stmt Δ Γ ρ → Bool
  | .return_void _
  | .return_tau _
  | .error _       => true
  | _ => acc
@[simp] def Returns.expr (τ : Typ) (acc : Bool) : Expr Δ Γ τ → Option Bool :=
  fun _ => some acc
@[simp] def Returns.lval (τ : Typ) (acc : Bool) : LValue Δ Γ τ → Option Bool :=
  fun _ => some acc
@[simp] def Returns.join (acc₁ acc₂ : Bool) : Stmt Δ Γ ρ → Option Bool
  | .while _ _ _ => some acc₁ -- acc₂ is the result of the body, we disregard
  | .ite _ _ _   => some (acc₁ && acc₂)
  | _            => some acc₂
@[simp] def Returns.Predicate : Stmt.Predicate Δ Γ Bool :=
  { init := fun acc s => (some (init acc s))
  , stmt := fun acc s => (some (stmt acc s))
  , lval
  , expr
  , join
  }

@[simp] def Returns.Stmt (stmt : Tst.Stmt Δ Γ ρ) rets rets' :=
  Stmt.Fold Returns.Predicate rets stmt rets'
@[simp] def Returns.Stmt.List (stmts : Tst.Stmt.List Δ Γ ρ) rets rets' :=
  Stmt.List.Fold Returns.Predicate rets stmts rets'

@[simp] theorem Returns.expr_fold
  : ∀ acc (e : Expr Δ Γ τ), Expr.Fold Returns.expr acc e acc := by
  intro acc e
  have p : ∀ τ (e' : Expr Δ Γ τ), Returns.expr τ acc e' = some acc := by simp
  induction e with -- is there a better way to do with?
  | num _       => exact .num   (p _ _)
  | char _      => exact .char  (p _ _)
  | str _       => exact .str   (p _ _)
  | var _ _     => exact .var   (p _ _)
  | «true»      => exact .true  (p _ _)
  | «false»     => exact .false (p _ _)
  | null        => exact .null  (p _ _)
  | unop        => next ih          => exact .unop ih                 (p _ _)
  | binop_int   => next ih₁ ih₂     => exact .binop_int   ih₁ ih₂     (p _ _)
  | binop_bool  => next ih₁ ih₂     => exact .binop_bool  ih₁ ih₂     (p _ _)
  | binop_eq    => next ih₁ ih₂     => exact .binop_eq    ih₁ ih₂     (p _ _)
  | binop_rel₁  => next ih₁ ih₂     => exact .binop_rel₁  ih₁ ih₂     (p _ _)
  | binop_rel₂  => next ih₁ ih₂     => exact .binop_rel₂  ih₁ ih₂     (p _ _)
  | ternop      => next ih₁ ih₂ ih₃ => exact .ternop      ih₁ ih₂ ih₃ (p _ _)
  | app         => next ih          => exact .app         ih          (p _ _)
  | alloc       => next             => exact .alloc                   (p _ _)
  | alloc_array => next ih          => exact .alloc_array ih          (p _ _)
  | dot         => next ih          => exact .dot         ih          (p _ _)
  | deref       => next ih          => exact .deref       ih          (p _ _)
  | index       => next ih₁ ih₂     => exact .index       ih₁ ih₂     (p _ _)
  | result      => next             => exact .result                  (p _ _)
  | length      => next ih          => exact .length      ih          (p _ _)

@[simp] theorem Returns.lval_fold
  : ∀ acc (lv : LValue Δ Γ τ),
    LValue.Fold (Δ := Δ) (Γ := Γ) Predicate.toLValuePred acc lv acc := by
  intro acc lv
  simp
  induction lv with -- is there a better way to do with?
  | var   => exact .var (by simp)
  | dot   => next ih => exact .dot   ih (by simp)
  | deref => next ih => exact .deref ih (by simp)
  | index _ e => next ih =>
    have : Expr.Fold Predicate.toLValuePred.expr acc e.val acc := by simp
    exact .index (a₃ := acc) ih this (by simp)

@[simp] theorem Returns.anno_fold
  : ∀ acc (anno : Anno Δ Γ),
    Anno.Fold (Δ := Δ) (Γ := Γ) Returns.expr acc anno acc := by
  intro acc anno
  cases anno with
  | requires   => exact .requires   (by simp)
  | ensures    => exact .ensures    (by simp)
  | loop_invar => exact .loop_invar (by simp)
  | assert     => exact .assert     (by simp)

@[simp] theorem Returns.anno_list_fold
  : ∀ acc (annos : List (Anno Δ Γ)),
    Anno.List.Fold (Δ := Δ) (Γ := Γ) Returns.expr acc annos acc := by
  intro acc annos
  induction annos with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (by simp) ih


structure SDef where
  name : Symbol
  fields : List (Typed Symbol)

structure FDecl (Δ : GCtx) where
  ret    : Option Typ
  name   : Symbol
  params : List (Typed Symbol)
  init_Γ : FCtx
  annos  : List (Anno.Function Δ init_Γ)
  initial_init : Initialised.Acc := Initialised.Acc.ofList (params.map (·.data))
  annos_init   : Initialised.Anno.List (annos.map (·.val)) initial_init

structure FDef (Δ : GCtx) extends FDecl Δ where
  body : Stmt.List Δ (init_Γ.addFunc name (Typ.flattenOpt ret) params) ret
  post_init : Initialised.Acc
  body_init : Initialised.Stmt.List body initial_init post_init
  body_rets : Returns.Stmt.List body false true

def GCtx.updateStruct (Δ : GCtx) (s : SDef) : GCtx :=
  let sig := ⟨Typed.toMap s.fields, true⟩
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
  | .char c      => s!"('{c.toString.sanitise}' : {τ})"
  | .str s       => s!"(\"{s.sanitise}\" : {τ})"
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
    s!"declare_init({name}, {init},\n  {str_body}\n)"
  | .assign_var lv _ v _
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
  | .return_void _ => s!"return"
  | .return_tau e  => s!"return {e}"
  | .assert e      => s!"assert{e}"
  | .error e       => s!"error{e}"
  | .expr e        => s!"{e}"
  | .anno a        => Anno.toString a.val

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
    let string_str := prog.strings.map (·.sanitise)
      |> String.intercalate "\n  - "
    let prog_str := prog.header.toStrings ++ prog.body.toStrings
      |> "\n\n".intercalate
    s!"-----  Calls  -----\n  {calls_str}\n
----- Strings -----\n  - {string_str}\n
----- Program -----\n\n{prog_str}\n
----- ------- -----\n"
