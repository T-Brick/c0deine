/- C0deine - TST.Dynamics.Preservation
   Proof of preservation of C0 dynamic semantics
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Dynamics.Step
import C0deine.Type.SyntaxTree.Dynamics.Notation

namespace C0deine.Tst.Dynamics

open Notation

/- Executing C0 code will never yield an "invalid" state:
      s valid ∧ s ==> s' → s' valid
-/
