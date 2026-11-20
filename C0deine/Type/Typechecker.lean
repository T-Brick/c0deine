/- C0deine - Typechecker
   Converts the AST to the TST by dealiasing and annotating expressions with
   types. Any NWT programs are rejected.
   - Thea Brick
 -/
import C0deine.Type.Checker.Context
import C0deine.Type.Checker.Validation
import C0deine.Type.Checker.Expr
import C0deine.Type.Checker.LValue
import C0deine.Type.Checker.Anno
import C0deine.Type.Checker.Stmt
import C0deine.Type.Checker.Global

namespace C0deine.Typechecker

@[macro_inline]
def main_func_status : Status.Symbol := .func ⟨⟨some (.prim .int), []⟩, false⟩

@[macro_inline]
def init_context : GlobalCtx := {
    symbols := Std.HashMap.emptyWithCapacity.insert Symbol.main main_func_status
    structs := Std.HashMap.emptyWithCapacity
    calls := Std.HashMap.emptyWithCapacity
    funcCalls := Std.HashMap.emptyWithCapacity
    strings := []
  }

def update_call_purity
    (func_calls : Symbol.Map Tst.Calls)
    (pure_calls : Tst.Calls)
    : Tst.Calls :=
  let only_pure := pure_calls.toList.filterMap (fun (f, is_pure) =>
    if is_pure then some f else none
  )
  let fuel := func_calls.size
  work fuel pure_calls {} only_pure
where work
    (fuel : Nat)
    (calls : Tst.Calls)
    (visited : Std.HashSet Symbol)
    (worklist : List Symbol) :=
  if fuel = 0 then calls else
  match worklist with
  | .nil => calls
  | f :: fs =>
    let calls := calls.insert f true
    let visited := visited.insert f
    let new_worklist := func_calls.getD f {}
      |>.toList
      |>.foldl (fun acc (g, _) =>
        if g ∉ visited && g ∉ fs then g :: acc else acc
      ) fs
    work (fuel - 1) calls visited new_worklist

def typecheck (prog : Ast.Prog) : Except Error Tst.Prog := do
  let init_acc : Global.Result.List {} := ⟨init_context, {}, .nil⟩
  let hres ← prog.header.foldlM (Global.gdecs true) init_acc
  let bres ← prog.program.foldlM (Global.gdecs false) ⟨hres.ctx, hres.Δ', .nil⟩

  let () ← Validate.callsDefined bres.ctx Symbol.main

  let calls := bres.ctx.calls.insert Symbol.main false
  let pure_funcs := update_call_purity bres.ctx.funcCalls calls

  let prog := {
    header_ctx := hres.Δ'
    header     := hres.gdecls
    body_ctx   := bres.Δ'
    body       := bres.gdecls
    pure_funcs := pure_funcs
    func_calls := bres.ctx.funcCalls
    strings    := bres.ctx.strings
  }
  return prog
