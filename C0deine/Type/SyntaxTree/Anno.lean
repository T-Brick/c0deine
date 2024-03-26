/- C0deine - TST.Anno
   Annotations help with reasoning about C0 code. Structurally enforced to be
   well typed.
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Expr

namespace C0deine.Tst

open Typ

open Typ.Notation in
inductive Anno (Δ : GCtx) (Γ : FCtx) : Type
| requires   : τ = (bool) → Expr.NoResult Δ Γ τ → Anno Δ Γ
| ensures    : τ = (bool) → Expr          Δ Γ τ → Anno Δ Γ
| loop_invar : τ = (bool) → Expr.NoResult Δ Γ τ → Anno Δ Γ
| assert     : τ = (bool) → Expr.NoResult Δ Γ τ → Anno Δ Γ

-- only requires/ensures can annotate functions
@[inline, reducible] def Anno.function : Anno Δ Γ → Bool
  | .requires _ _   => true
  | .ensures _ _    => true
  | .loop_invar _ _ => false
  | .assert _ _     => false

-- only loop_invariant and assert can annotate loops
@[inline, reducible] def Anno.loop : Anno Δ Γ  → Bool
  | .requires _ _   => false
  | .ensures _ _    => false
  | .loop_invar _ _ => true
  | .assert _ _     => false -- see language deviation

-- only assert can be not attatched to a loop/function
@[inline, reducible] def Anno.free : Anno Δ Γ  → Bool
  | .requires _ _   => false
  | .ensures _ _    => false
  | .loop_invar _ _ => false
  | .assert _ _     => true

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
  → {hτ : τ = (bool)}
  → {e : Expr.NoResult Δ Γ τ}
  → Expr.Fold P a₁ e.val a₂
  → Anno.Fold P a₁ (.requires hτ e) a₂
| ensures
  : {a₁ a₂ : α}
  → {hτ : τ = (bool)}
  → {e : Expr Δ Γ τ}
  → Expr.Fold P a₁ e a₂
  → Anno.Fold P a₁ (.ensures hτ e) a₂
| loop_invar
  : {a₁ a₂ : α}
  → {hτ : τ = (bool)}
  → {e : Expr.NoResult Δ Γ τ}
  → Expr.Fold P a₁ e.val a₂
  → Anno.Fold P a₁ (.loop_invar hτ e) a₂
| assert
  : {a₁ a₂ : α}
  → {hτ : τ = (bool)}
  → {e : Expr.NoResult Δ Γ τ}
  → Expr.Fold P a₁ e.val a₂
  → Anno.Fold P a₁ (.assert hτ e) a₂

inductive Anno.List.Fold
    : (P : (τ : Typ) → α → Expr Δ Γ τ → Option α)
    → α → List (Anno Δ Γ) → α → Prop
| nil : Anno.List.Fold P a [] a
| cons
  : Anno.Fold P a₁ anno a₂
  → Anno.List.Fold P a₂ annos a₃
  → Anno.List.Fold P a₁ (anno :: annos) a₃

def Anno.toString : Anno Δ Γ → String
  | .requires _ e   => s!"//@requires {e}"
  | .ensures _ e    => s!"//@ensures {e}"
  | .loop_invar _ e => s!"//@loop_invariant {e}"
  | .assert _ e     => s!"//@assert {e}"
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
