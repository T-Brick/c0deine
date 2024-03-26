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


theorem Step.State.mk_iff_result_eq {p : Prog} {r₁ r₂ : DynResult} :
    r₁ = r₂ ↔ State.mk (p := p) H S η r₁ = State.mk H S η r₂ := by
  apply Iff.intro <;> intro h₁
  . simp only [State.mk.injEq, DynResult.val.injEq, true_and, h₁]
  . simp only [State.mk.injEq, true_and] at h₁
    exact h₁


theorem Step.val_deterministic {p : Prog} {s₁ s₂ : State p}
    (h₁ : Step { H := H, S := S, η := η, r := DynResult.val v K } s₁)
    (h₂ : Step { H := H, S := S, η := η, r := DynResult.val v K } s₂)
    : s₁ = s₂ := by
  cases h₁ <;> cases h₂ <;> try (
    apply Step.State.mk_iff_result_eq.mp
    simp
    first
    | exact Step.UnOp.deterministic (by assumption) (by assumption)
    | exact Sum.inl.inj (Step.BinOp.Int.deterministic (by assumption) (by assumption))
    | exact Sum.inr.inj (Step.BinOp.Int.deterministic (by assumption) (by assumption))
    | exact Step.BinOp.Cmp.deterministic (by assumption) (by assumption)
    | next h' _exn h'' =>
        have := Step.BinOp.Int.deterministic h' h''
        contradiction
    | skip
  )
  all_goals sorry

theorem Step.eval_deterministic {p : Prog} {s₁ s₂ : State p}
    (h₁ : Step { H := H, S := S, η := η, r := DynResult.eval e K } s₁)
    (h₂ : Step { H := H, S := S, η := η, r := DynResult.eval e K } s₂)
    : s₁ = s₂ := by
  sorry

theorem Step.deterministic {p : Prog} {s s₁ s₂ : State p}
    (h₁ : Step s s₁) (h₂ : Step s s₂) : s₁ = s₂ := by
  let ⟨H, S, η, r⟩ := s
  cases r
  case val Δ Γ τ v K     => exact Step.val_deterministic h₁ h₂
  case eval Δ Γ τ rk e K => exact Step.eval_deterministic h₁ h₂
  case exec Δ Γ ρ rk s K => sorry
  case exec_seq          => cases h₁
  case exn               => cases h₁
  case nop               => cases h₁
  case res               => cases h₁
