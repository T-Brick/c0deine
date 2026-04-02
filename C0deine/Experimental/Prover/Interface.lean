/- C0deine - Prover.Interface
   Components that interface with the compiler frontend
   - Thea Brick
 -/
import C0deine.Top
import C0deine.Ast.Ast
import C0deine.Type.SyntaxTree.Dynamics
import C0deine.Experimental.Prover.SyntaxTree.Pst
import C0deine.Experimental.Prover.SyntaxTree.Notation
import C0deine.Type.SyntaxTree.Dynamics.Notation
-- import C0deine.Experimental.Prover.Tactics

namespace C0deine.Prover

open Tst.Dynamics

def parse_tc (prog : String) : Option (Tst.Prog × Context.State) := do
  -- let libSearchDirs ← mkLibSearchDirs [] []
  let config : Config := default
    -- { (default : Config) with libSearchDirs := libSearchDirs }
  let  (tst, _config, ctx) ← Top.runFrontendNoIO config prog
  return (tst, ctx)

def parse_tc! (prog : String) : Tst.Prog × Context.State :=
  match parse_tc prog with
  | none => panic! "Could not typecheck program!"
  | some res => res


def get_body (prog_ctx : Tst.Prog × Context.State) (func : String) := do
  let (prog, ctx) := prog_ctx
  let ⟨_Δ, fdef⟩ ← prog.findFuncDef (ctx.symbolCache.get! func)
  let dyn_res := DynResult.exec_seq fdef.body.toList .nil
  return dyn_res

open Lean Elab Command Term Meta

-- syntax "#c0_prove" term "," term : command

-- macro_rules
-- | `(#c0_prove $p:term , $f:term ) =>
--   `(def x := 5
--    )

open C0deine.Tst.Dynamics.Notation

def _root_.Except.get! [Inhabited α] [ToString ε] : Except ε α → α
| .ok a => a
| .error e => panic! (toString e)

def toTst! (Γ : Tst.FCtx) (stmts : List Pst.Stmt) : List (Tst.Stmt Δ Γ ρ) :=
  stmts.mapM (Pst.Stmt.toTst Γ) |>.get!

open Qq in
elab "c0_init_proof" f:term : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let func ← do
      let func ← Term.elabTerm f (some q(String))
      unsafe evalExpr (String) (q(String)) func
    Lean.Elab.Tactic.evalTactic (← `(tactic|
        constructor; constructor; constructor
      ))
    let goals ← Lean.Elab.Tactic.getGoals
    let _ ← goals.mapIdxM (fun n goal =>
        match n with
        | 0 => goal.setUserName (.mkSimple s!"`{func}`")
        | 1 => goal.setUserName (.mkSimple "env")
        | 2 => goal.setUserName (.mkSimple "stack")
        | 3 => goal.setUserName (.mkSimple "heap")
        | _ => pure ()
      )

open Qq in
elab "c0_theorem" n:declId ":" "prove" f:term "in" p:term ":= " b:tacticSeq : command => do
  let (prog, ctx) ← liftTermElabM do
    let τ := Tst.Prog × Context.State
    let prog ← Term.elabTerm p (some q(Tst.Prog × Context.State))
    unsafe evalExpr τ (q(Tst.Prog × Context.State)) prog

  let func ← liftTermElabM do
    let func ← Term.elabTerm f (some q(String))
    unsafe evalExpr (String) (q(String)) func


  match prog.findFuncDef (ctx.symbolCache.get! func) with
  | none => throwError s!"Could not find function ${func}"
  | some ⟨Δ, fdef⟩ =>
    logInfo s!"{fdef.body}"
    let progPst ← liftTermElabM do
      -- TODO need to implement notation
      let pst := Pst.Prog.ofTst prog
      return ← Lean.PrettyPrinter.delab (Lean.toExpr pst)
    let bodyPst ← liftTermElabM do
      let pst := (Pst.FDef.ofTst fdef).body
      return ← Lean.PrettyPrinter.delab (Lean.toExpr pst)
    let cmd ← `(
      -- TODO delab/convert to PST: p Γ Δ
      theorem $n {p Γ Δ} : ∃ H S η,
        ({}; {}; {} |= (.exec_seq (ρ := .some (.prim .int)) (Δ := Δ) (toTst! Γ $bodyPst) .nil) [prog|p])
   ==>* (H; S; η |= (.val (Δ:=Δ) (Γ:=Γ) (.num 150) .nil) [prog|p]) := by
        c0_init_proof $f
        ($b)
    )
    elabCommand cmd

def prog₁_string := "
int main() {
  int x = 100 + 5 * 10;
  //@assert x == 150;
  return x;
}"

def prog₁ := parse_tc! prog₁_string


c0_theorem test : prove "main" in prog₁ :=
  all_goals sorry
