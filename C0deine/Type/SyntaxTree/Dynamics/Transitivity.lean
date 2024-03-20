/- C0deine - TST.Dynamics.Transitivity
   Proof of transitivity of C0 dynamic semantics
      s₁ ==>* s₂ ∧ s₂ ==>* s₃ → s₁ ==>* s₃
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Dynamics.Step

namespace C0deine.Tst.Dynamics

theorem Steps.trans (h₁ : Steps s₁ s₂) (h₂ : Steps s₂ s₃) : Steps s₁ s₃ := by
  let ⟨n₁, h₁⟩ := h₁
  let ⟨n₂, h₂⟩ := h₂
  refine ⟨n₁ + n₂, ?_⟩
  match n₂ with
  | 0 =>
    simp [StepsN] at h₂ ⊢
    rw [h₂] at h₁
    exact h₁
  | n₂ + 1 =>
    induction n₂ generalizing s₃ with
    | zero =>
      cases n₁ <;> simp [StepsN]
      . cases h₁; exact h₂
      . exact ⟨s₂, h₁, h₂⟩
    | succ n₂ ih =>
      let ⟨s₂', h₂'⟩ := h₂
      refine ⟨s₂', ?_, h₂'.right⟩
      exact ih ⟨_, h₂'.left⟩ h₂'.left

instance : Trans (Step  (p := p)) Step  Steps := ⟨(Steps.trans ⟨1, ·⟩ ⟨1, ·⟩)⟩
instance : Trans (Steps (p := p)) Step  Steps := ⟨(Steps.trans · ⟨1, ·⟩)⟩
instance : Trans (Step  (p := p)) Steps Steps := ⟨(Steps.trans ⟨1, ·⟩ ·)⟩
instance : Trans (Steps (p := p)) Steps Steps := ⟨Steps.trans⟩
