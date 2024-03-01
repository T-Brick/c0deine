/- C0deine - TST.Stmt
   Statements include the return type of the function they are in to allow for
   proper type checking.
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Expr
import C0deine.Type.SyntaxTree.LValue
import C0deine.Type.SyntaxTree.Anno

namespace C0deine.Tst

open Typ

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

def Stmt.List.append (s₁ s₂ : Stmt.List Δ Γ ρ) : Stmt.List Δ Γ ρ :=
  Stmt.List.ofList (s₁.toList ++ s₂.toList)

instance : Coe (Stmt.List Δ Γ ρ) (List (Stmt Δ Γ ρ)) := ⟨Stmt.List.toList⟩

instance : HAppend (Stmt.List Δ Γ ρ) (Stmt.List Δ Γ ρ) (Stmt.List Δ Γ ρ) :=
  ⟨Stmt.List.append⟩
instance : HAppend (Stmt.List Δ Γ ρ) (List (Stmt Δ Γ ρ)) (Stmt.List Δ Γ ρ) :=
  ⟨fun s l => Stmt.List.append s (Stmt.List.ofList l)⟩
instance : HAppend (List (Stmt Δ Γ ρ)) (Stmt.List Δ Γ ρ) (Stmt.List Δ Γ ρ) :=
  ⟨fun l s => Stmt.List.append (Stmt.List.ofList l) s⟩

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
