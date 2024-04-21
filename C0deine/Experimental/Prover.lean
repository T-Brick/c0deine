/- C0deine - Prover
   Experimental tool for proving C0 code correct.
   - Thea Brick
 -/
import C0deine.Top
import C0deine.Type.SyntaxTree.Dynamics
import C0deine.Type.SyntaxTree.Dynamics.Notation
import C0deine.Type.SyntaxTree.Dynamics.Transitivity
import C0deine.Ast.Ast

namespace C0deine.Prover

open Top

def parse_tc (prog : String) : Option (Tst.Prog × Context.State) := do
  -- let libSearchDirs ← mkLibSearchDirs [] []
  let config : Config := default
    -- { (default : Config) with libSearchDirs := libSearchDirs }
  let  (tst, _config, ctx) ← runFrontendNoIO config prog
  return (tst, ctx)

def parse_tc! (prog : String) : Tst.Prog × Context.State :=
  match parse_tc prog with
  | none => panic! "Could not typecheck program!"
  | some res => res


def verify (prog : Tst.Prog) (ctx : Context.State) (func : String) := do
  let fdef ← prog.findFuncDef (ctx.symbolCache.find! func)
  return ()



namespace Testing

def prog₁ := parse_tc! "
int main() {
  int x = 150;
  //@assert x == 150;
  return 150;
}"

#eval prog₁.1

def test_ast := Ast.Expr.binop (.int .plus) (.num 5) (.num 5)

macro "c0_step_expr_setup" : tactic =>
  `(tactic| ( apply Tst.Dynamics.Steps.trans
              apply Exists.intro 1
              apply Tst.Dynamics.Step.expr
            )
   )

macro "c0_step_self" : tactic => `(tactic| exact ⟨0, by rfl⟩)

macro "c0_step_one_setup" : tactic =>
  `(tactic| ( apply Tst.Dynamics.Steps.trans
              apply Exists.intro 1
            )
   )

elab "c0_step" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goal_type ← goal.getType''

    -- check if we need to split a sequence of steps into one step
    if goal_type.isAppOf `C0deine.Tst.Dynamics.Steps then
      Lean.Elab.Tactic.evalTactic (← `(tactic| try c0_step_self))

      if (← Lean.Elab.Tactic.getGoals).isEmpty then return
      -- could not step to self, there must be one more step
      Lean.Elab.Tactic.evalTactic (← `(tactic| c0_step_one_setup))

    -- try stepping the code
    let get_dyn_res : Lean.Expr → _ :=
      fun goal_type => do (← goal_type.getArg? 1).getArg? 4

    let goal ← Lean.Elab.Tactic.getMainGoal
    let goal_type ← goal.getType'
    let dyn_res ← get_dyn_res goal_type

    match dyn_res.getAppFn with
    | .const `C0deine.Tst.Dynamics.DynResult.val _
    | .const `C0deine.Tst.Dynamics.DynResult.eval _ =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply Tst.Dynamics.Step.expr))
      let goal ← Lean.Elab.Tactic.getMainGoal
      let goal_type ← goal.getType'
      let dyn_res ← get_dyn_res goal_type
      let expr ← dyn_res.getArg? 4

      match expr.getAppFn with
      | .const expr_name _ =>
        match expr_name.componentsRev with
        | `binop_int :: _
        | `binop_int₁ :: _ =>
          Lean.Elab.Tactic.evalTactic (← `(tactic| apply Tst.Dynamics.Step.Expr.binop))
          Lean.Elab.Tactic.evalTactic (← `(tactic| constructor))
        | `binop_int₂ :: _ =>
          Lean.Elab.Tactic.evalTactic (← `(tactic| apply Tst.Dynamics.Step.Expr.binop))
          Lean.Elab.Tactic.evalTactic (← `(tactic| constructor))
          Lean.Elab.Tactic.evalTactic (← `(tactic| constructor))
        | test =>
          -- dbg_trace f!"Expr name: {expr_name}"
          -- dbg_trace f!"Expr name last: {test}"
          Lean.Elab.Tactic.evalTactic (← `(tactic| constructor))
      | _ =>
        Lean.Meta.throwTacticEx `c0_step goal "Could not find C0 dynamic state"
    | dyn_mode =>
      dbg_trace f!"TODO: {dyn_mode} | type: {goal_type}"
    -- dbg_trace f!""

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
