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

def typecheck (prog : Ast.Prog) : Except Error Tst.Prog := do
  let main_info := .func ⟨⟨some (.prim .int), []⟩, false⟩
  let main_sym := Symbol.main

  let init_symbols := Std.HashMap.empty.insert main_sym main_info
  let init_calls := Std.HashMap.empty.insert main_sym false
  let init_context : GlobalCtx :=
    ⟨init_symbols, Std.HashMap.empty, init_calls, Std.HashMap.empty, []⟩
  let init_acc : Global.Result.List {} := ⟨init_context, {}, .nil⟩

  let hres ← prog.header.foldlM (Global.gdecs true) init_acc
  let bres ← prog.program.foldlM (Global.gdecs false) ⟨hres.ctx, hres.Δ', .nil⟩

  let () ← Validate.callsDefined bres.ctx main_sym
  let prog :=
    { header_ctx := hres.Δ'
    , header     := hres.gdecls
    , body_ctx   := bres.Δ'
    , body       := bres.gdecls
    , calls      := bres.ctx.calls
    , strings    := bres.ctx.strings
    }
  return prog
