/- C0deine - Prover.Playground
   Testing area for verifying C0 code
   - Thea Brick
 -/
import C0deine.Experimental.Prover.Interface
import C0deine.Experimental.Prover.Tactics

namespace C0deine.Prover.Playground

def prog₁ := parse_tc! "
int main() {
  int x = 150;
  //@assert x == 150;
  return x;
}"

open Typ.Notation in
def tst : Tst.Expr {} {} (int) :=
  Tst.Expr.binop_int (by rfl) (by rfl) (by rfl)
    .plus (.num (by rfl) 5) (.num (by rfl) 5)

open Tst.Dynamics Notation in
example /-  5 + 5 ==>* 10   -/
       : (H; S; η |= (.eval tst .nil)                       [prog|p])
    ==>* (H; S; η |= (.val (Δ:={}) (Γ:={}) (.num 10) .nil)  [prog|p])
    := by
  rw [tst]
  repeat c0_step
