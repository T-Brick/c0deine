/- C0deine - Prover
   Experimental tool for proving C0 code correct.
   - Thea Brick
 -/
import C0deine.Top
import C0deine.Type.SyntaxTree.Dynamics

namespace C0deine.Prover

open Top

def parse_tc (prog : String) : IO (Option (Tst.Prog × Context.State)) := do
  let libSearchDirs ← mkLibSearchDirs [] []
  let config : Config :=
    { (default : Config) with libSearchDirs := libSearchDirs }
  match ← runFrontend config (fun _ => pure ()) [] [] (some prog) with
  | none =>
    IO.println "Could not typecheck program!"
    return none
  | some (tst, _config, ctx) => return some (tst, ctx)

def parse_tc! (prog : String) : IO (Tst.Prog × Context.State) := do
  match ← parse_tc prog with
  | none => panic! "Could not typecheck program!"
  | some res => return res


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

#eval (prog₁ >>= (fun (tst, _ctx) => pure (toString tst))).run ()

