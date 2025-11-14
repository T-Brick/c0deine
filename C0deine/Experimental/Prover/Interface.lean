/- C0deine - Prover.Interface
   Components that interface with the compiler frontend
   - Thea Brick
 -/
import C0deine.Top
import C0deine.Ast.Ast
import C0deine.Type.SyntaxTree.Dynamics
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

open Qq in
elab "c0_theorem" n:declId ":" "prove" f:term "in" p:term ":=" b:term : command => do
  let (prog, ctx) ← liftTermElabM do
    let τ := Tst.Prog × Context.State
    let prog ← Term.elabTerm p (some q(Tst.Prog × Context.State))
    unsafe evalExpr τ (q(Tst.Prog × Context.State)) prog

  let func ← liftTermElabM do
    let func ← Term.elabTerm f (some q(String))
    unsafe evalExpr (String) (q(String)) func


  match prog.findFuncDef (ctx.symbolCache.get! func) with
  | none => throwError s!"Could not find function ${func}"
  | some ⟨_Δ, fdef⟩ =>
    logInfo s!"{fdef.body}"
    -- let test : Expr := Lean.toExpr fdef
    let cmd ← `(
      theorem $(n) : $(quote true) = true :=
        $b
    )
    elabCommand cmd

def prog₁_string := "
int main() {
  int x = 150;
  //@assert x == 150;
  return x;
}"

def prog₁ := parse_tc! prog₁_string

c0_theorem test : prove "main" in prog₁ := by
  sorry
