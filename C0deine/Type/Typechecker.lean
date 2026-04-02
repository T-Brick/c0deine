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
    calls := Std.HashMap.emptyWithCapacity.insert Symbol.main false
    funcCalls := Std.HashMap.emptyWithCapacity
    strings := []
  }

def typecheck (prog : Ast.Prog) : Except Error Tst.Prog := do
  let init_acc : Global.Result.List {} := ⟨init_context, {}, .nil⟩
  let hres ← prog.header.foldlM (Global.gdecs true) init_acc
  let bres ← prog.program.foldlM (Global.gdecs false) ⟨hres.ctx, hres.Δ', .nil⟩

  let () ← Validate.callsDefined bres.ctx Symbol.main
  let prog := {
    header_ctx := hres.Δ'
    header     := hres.gdecls
    body_ctx   := bres.Δ'
    body       := bres.gdecls
    calls      := bres.ctx.calls
    strings    := bres.ctx.strings
  }
  return prog
