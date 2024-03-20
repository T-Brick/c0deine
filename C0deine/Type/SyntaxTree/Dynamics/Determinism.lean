/- C0deine - TST.Dynamics.Determinism
   Proof of determinism of C0 dynamic semantics
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Dynamics.Step
import C0deine.Type.SyntaxTree.Dynamics.Notation

namespace C0deine.Tst.Dynamics

open Notation

/- There is exactly one way to execute C0 code:
      s ==> s₁ ∧ s ==> s₂ → s₁ = s₂
-/
