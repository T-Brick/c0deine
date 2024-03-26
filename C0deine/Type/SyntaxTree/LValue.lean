/- C0deine - TST.LValue
   LValues or expressions that appear on the left of assignments. These must be
   well typed by definition.
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Expr

namespace C0deine.Tst

open Typ

open Typ.Notation in
inductive LValue (Δ : GCtx) (Γ : FCtx) : Typ → Type
| var   : (x : Symbol)
        → (Γ.syms x = .some (.var τ))
        → LValue Δ Γ τ
| dot   : (hτ₁ : τ₁ = (struct s))
        → LValue Δ Γ τ₁
        → (field : Symbol)
        → Δ.struct s = .some ⟨fields, true⟩
        → fields field = .some τ
        → LValue Δ Γ τ
| deref : (hτ₁ : τ₁ = (τ*))
        → LValue Δ Γ τ₁
        → LValue Δ Γ τ
| index : (hτ₁ : τ₁ = (τ[]))
        → (hτ₂ : τ₂ = (int))
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
  | .var name _       => name
  | .dot _ _ _ _ _
  | .deref _ _
  | .index _ _ _ _    => by simp [is_var] at h₁


structure Predicate (Δ : GCtx) (Γ : FCtx) (α : Type) where
  lval : (τ : Typ) → α → LValue Δ Γ τ → Option α
  expr : (τ : Typ) → α → Expr Δ Γ τ → Option α

/- Assert that some predicate P applies to every sub-lvalue -/
inductive Fold : {Δ : GCtx} → {Γ : FCtx}
  → (P : LValue.Predicate Δ Γ α) → α → LValue Δ Γ τ → α → Prop
| var
  : {a₁ a₂ : α}
  → {P : LValue.Predicate Δ Γ α}
  → {h : Γ.syms x = .some (.var τ)}
  → P.lval _ a₁ (.var x h) = some a₂
  → Fold P a₁ ((.var x h) : LValue Δ Γ _) a₂
| dot
  : {a₁ a₂ : α}
  → {hτ₁ : τ₁ = (struct s)}
  → Fold P a₁ l a₂
  → P.lval _ a₂ (.dot hτ₁ l f h₁ h₂) = some a₃
  → Fold P a₁ (.dot hτ₁ l f h₁ h₂) a₃
| deref
  : {hτ₁ : τ₁ = (τ*)}
  → Fold P a₁ l a₂
  → P.lval _ a₂ (.deref hτ₁ l) = some a₃
  → Fold P a₁ (.deref hτ₁ l) a₃
| index
  : {hτ₁ : τ₁ = (τ[])}
  → {hτ₂ : τ₂ = (int)}
  → {l : LValue Δ Γ τ₁}
  → Fold P a₁ l a₂
  → Expr.Fold P.expr a₂ e.val a₃
  → P.lval _ a₃ (.index hτ₁ hτ₂ l e) = some a₄
  → Fold P a₁ (.index hτ₁ hτ₂ l e) a₄

def toExpr {τ : Typ} : LValue Δ Γ τ → Expr Δ Γ τ
  | .var x h        => .var x h
  | .dot hτ₁ lv f h₁ h₂ => .dot hτ₁ lv.toExpr f h₁ h₂
  | .deref hτ₁ lv       => .deref hτ₁ lv.toExpr
  | .index hτ₁ hτ₂ lv ind   =>
    .index hτ₁ hτ₂ lv.toExpr ind.val

end LValue

def LValue.toString : LValue Δ Γ τ → String
  | .var name _        => s!"({name} : {τ})"
  | .dot _ e field _ _ => s!"({LValue.toString e}.{field} : {τ})"
  | .deref _ e         => s!"(*{LValue.toString e} : {τ})"
  | .index _ _ e i     => s!"({LValue.toString e}[{i}] : {τ})"

instance : ToString (LValue Δ Γ τ) where toString := LValue.toString
instance : ToString (List (Typed Symbol)) where
  toString tss := tss.map Typed.toString |> String.intercalate ", "
