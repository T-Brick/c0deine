/- C0deine - Prover.Playground
   Testing area for verifying C0 code
   - Thea Brick
 -/
import C0deine.Top
import C0deine.Experimental.Prover.Interface
import C0deine.Experimental.Prover.Tactics
import C0deine.Experimental.Prover.SyntaxTree.Pst
import C0deine.Experimental.Prover.SyntaxTree.Notation

namespace C0deine.Prover.Playground

def prog₁_string := "
int main() {
  int x = 100 + 5 * 10;
  //@assert x == 150;
  return x;
}"

def prog₁ := parse_tc! prog₁_string

open Typ.Notation in
def tst : Tst.Expr {} {} (int) :=
  Tst.Expr.binop_int (by rfl) (by rfl) (by rfl)
    .plus (.num (by rfl) 5) (.num (by rfl) 2)

open Tst.Dynamics Notation in
example /-  5 + 2 ==>* 7   -/
       : (H; S; η |= (.eval tst .nil)                      [prog|p])
    ==>* (H; S; η |= (.val (Δ:={}) (Γ:={}) (.num 7) .nil)  [prog|p])
    := by
  rw [tst]
  c0_step
  c0_step
  c0_step
  c0_step
  c0_step
  c0_step

open C0deine.Tst.Dynamics.Notation

c0_theorem aa : prove "main" in prog₁ :=
  c0_step
  apply Tst.Dynamics.Step.stmt
  -- reduce at ⊢
  -- apply Tst.Dynamics.Step.Stmt.seq_cons
  all_goals sorry

open C0deine.Pst.Notation
def meep :=
  toTst! (Δ := {}) (ρ := .some (.prim .int))
    { syms := fun _ => .none, ret := .some (.prim .int) }
    [>>c0_stmt|
        int x₁ =
          (100 : int + ((5 : int) * 10 : int) : int) : int {
            //@assert (x₁ : int == 150 : int) : bool;
            return x₁ : int
            } <<]

#reduce toTst! (Δ := {}) (ρ := .some (.prim .int))
    { syms := fun _ => .none, ret := .some (.prim .int) }
    [>>c0_stmt|
        int x₁ =
          (100 : int + ((5 : int) * 10 : int) : int) : int {
            //@assert (x₁ : int == 150 : int) : bool;
            return x₁ : int
            } <<]
