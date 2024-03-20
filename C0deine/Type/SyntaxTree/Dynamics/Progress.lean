/- C0deine - TST.Dynamics.Progress
   Proof of progress of C0 dynamic semantics
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Dynamics.Step
import C0deine.Type.SyntaxTree.Dynamics.Notation

namespace C0deine.Tst.Dynamics

open Notation

/- From a valid state, we are either finished executing or can step
      s valid → s final ∨ ∃ s', s ==> s'
-/
