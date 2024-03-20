/- C0deine - TST.Dynamics.Transitivity
   Proof of transitivity of C0 dynamic semantics
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Dynamics.Step
import C0deine.Type.SyntaxTree.Dynamics.Notation

namespace C0deine.Tst.Dynamics

open Notation

/- Steps in the dynamic semantics of C0 are transitive:
      s₁ ==>* s₂ ∧ s₂ ==>* s₃ → s₁ ==>* s₃
-/
