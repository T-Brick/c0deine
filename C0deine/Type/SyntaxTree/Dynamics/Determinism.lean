/- C0deine - TST.Dynamics.Determinism
   Proof of determinism of C0 dynamic semantics:
      s ==> s₁ ∧ s ==> s₂ → s₁ = s₂
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Dynamics.Step

namespace C0deine.Tst.Dynamics

theorem Step.UnOp.deterministic {op : Tst.UnOp} {v v₁ v₂ : Value}
    (h₁ : Step.UnOp op v v₁) (h₂ : Step.UnOp op v v₂) : v₁ = v₂ := by
  cases h₁ <;> (cases h₂; rfl)

theorem Step.BinOp.Int.deterministic {op : Tst.BinOp.Int} {v₁ v₂ : Value}
    (h₁ : Step.BinOp.Int v₁ op v₂ r₁)
    (h₂ : Step.BinOp.Int v₁ op v₂ r₂)
    : r₁ = r₂ := by
  cases h₁ <;> (cases h₂; rfl)

theorem Step.BinOp.Cmp.deterministic {op : Comparator} {v₁ v₂ : Value}
    (h₁ : Step.BinOp.Cmp v₁ op v₂ r₁)
    (h₂ : Step.BinOp.Cmp v₁ op v₂ r₂)
    : r₁ = r₂ := by
  cases h₁ <;> (cases h₂; rfl)

theorem Step.BinOp.deterministic {p : Prog} {s s₁ s₂ : State p}
    (h₁ : Step.BinOp s s₁)
    (h₂ : Step.BinOp s s₂)
    : s₁ = s₂ := by
  cases h₁ <;> cases h₂ <;> try rfl
  all_goals (
    simp
    first
    | next h₁ _ h₂ =>
        have := Step.BinOp.Int.deterministic h₁ h₂
        first | exact Sum.inl.inj this
              | exact Sum.inr.inj this
              | contradiction
    | next h₁ _ h₂ =>
        have := Step.BinOp.Cmp.deterministic h₁ h₂
        assumption
  )

theorem Step.Expr.deterministic {p : Prog} {s s₁ s₂ : State p}
    (h₁ : Step.Expr s s₁)
    (h₂ : Step.Expr s s₂)
    : s₁ = s₂ := by
  sorry

theorem Step.State.mk_iff_result_eq {p : Prog} {r₁ r₂ : DynResult} :
    r₁ = r₂ ↔ State.mk (p := p) H S η r₁ = State.mk H S η r₂ := by
  apply Iff.intro <;> intro h₁
  . simp only [h₁]
  . simp only [State.mk.injEq, true_and] at h₁
    exact h₁



theorem Step.deterministic {p : Prog} {s s₁ s₂ : State p}
    (h₁ : Step s s₁) (h₂ : Step s s₂) : s₁ = s₂ := by
  let ⟨H, S, η, r⟩ := s
  cases r
  case val Δ Γ rk v K =>
    sorry
  case eval Δ Γ τ rk e K =>
    sorry
  case exec => sorry
  case exec_seq => sorry
  case exn => sorry
  case nop Δ Γ rk K =>
    cases h₁ <;> cases h₂
    all_goals sorry
  case res c =>
    sorry
