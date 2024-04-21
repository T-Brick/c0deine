/- C0deine - Prover.Interface
   Components that interface with the compiler frontend
   - Thea Brick
 -/
import C0deine.Top
-- import C0deine.Type.SyntaxTree.Dynamics
-- import C0deine.Type.SyntaxTree.Dynamics.Notation
-- import C0deine.Type.SyntaxTree.Dynamics.Transitivity
-- import C0deine.Experimental.Prover.Tactics

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


def verify (prog_ctx : Tst.Prog × Context.State) (func : String) := do
  let (prog, ctx) := prog_ctx
  let fdef ← prog.findFuncDef (ctx.symbolCache.find! func)
  return ()

