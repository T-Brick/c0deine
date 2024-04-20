/- C0deine - TST.Dynamics.Notation
   Notation for the dynamic semantics of C0 (specifically the TST).
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Dynamics.Step

namespace C0deine.Tst.Dynamics.Notation

scoped notation:50 H:51 " ; " S:51 " ; " η:51 " |= " r:51 " [prog| " p:51 " ] " =>
  State.mk (p:=p) H S η r
scoped notation:50 s₁:51 " ==> " s₂:51 => Step s₁ s₂
scoped notation:50 s₁:51 " ==>* " s₂:51 => Steps s₁ s₂

-- scoped notation:50 e:51 "▷" K:51 => DynResult.eval e K
