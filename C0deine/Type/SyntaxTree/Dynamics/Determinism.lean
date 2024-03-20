/- C0deine - TST.Dynamics.Determinism
   Proof of determinism of C0 dynamic semantics:
      s ==> s₁ ∧ s ==> s₂ → s₁ = s₂
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Dynamics.Step

namespace C0deine.Tst.Dynamics


theorem Step.deterministic {p : Prog} {s s₁ s₂ : State p}
    (h₁ : Step s s₁) (h₂ : Step s s₂) : s₁ = s₂ := by
  sorry
