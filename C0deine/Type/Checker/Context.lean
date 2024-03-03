/- C0deine - Type.Checker.Context
   Contexts, Error, and other utilities for typechecking
   - Thea Brick
 -/
import Std
import C0deine.Ast.Ast
import C0deine.Type.Typ
import C0deine.Type.Tst
import C0deine.Context.Symbol
import C0deine.Context.Context
import C0deine.Utils.Comparison

namespace C0deine.Typechecker

structure FuncType where
  ret : Option Typ
  args : List Typ

structure Status.Var where
  type        : Typ
  initialised : Bool

structure Status.Func where
  type    : FuncType
  defined : Bool

structure Status.Struct where
  fields  : Symbol.Map Typ
  defined : Bool

inductive Status.Symbol
| var   (v : Status.Var)
| func  (f : Status.Func)
| alias (type : Typ)

def SymbolTable := Symbol.Map Status.Symbol
def StructTable := Symbol.Map Status.Struct

class Ctx (α : Type) where
  symbols    : α → SymbolTable
  structs    : α → StructTable
  calls      : α → Tst.Calls
  strings    : α → List String

structure FuncCtx where
  name       : Symbol
  symbols    : SymbolTable
  structs    : StructTable
  calls      : Tst.Calls
  strings    : List String
  ret_type   : Option Typ
  returns    : Bool
instance : Ctx FuncCtx where
  symbols    := FuncCtx.symbols
  structs    := FuncCtx.structs
  calls      := FuncCtx.calls
  strings    := FuncCtx.strings

structure GlobalCtx where
  symbols    : SymbolTable
  structs    : StructTable
  calls      : Tst.Calls
  funcCalls  : Symbol.Map Tst.Calls
  strings    : List String

instance : Ctx GlobalCtx where
  symbols    := GlobalCtx.symbols
  structs    := GlobalCtx.structs
  calls      := GlobalCtx.calls
  strings    := GlobalCtx.strings


-- defaults to not returning
def GlobalCtx.toFuncCtx (name : Symbol)
                        (ret : Option Typ)
                        (ctx : GlobalCtx)
                        : FuncCtx :=
  { name     := name
  , symbols  := ctx.symbols
  , structs  := ctx.structs
  , calls    := ctx.calls
  , strings  := ctx.strings
  , ret_type := ret
  , returns  := false
  }

def FuncCtx.toGlobalCtx (ctx : FuncCtx) : GlobalCtx :=
  { symbols   := ctx.symbols
  , structs   := ctx.structs
  , calls     := ctx.calls
  , funcCalls := Std.HashMap.empty.insert ctx.name ctx.calls
  , strings   := ctx.strings
  }

-- joins two contexts together, assuming non-variables are the same
def FuncCtx.join (ctx1 ctx2 : FuncCtx) : FuncCtx :=
  let returns := ctx1.returns && ctx2.returns
  let calls := ctx1.calls.merge ctx2.calls
  let intersect :=
    fun var status =>
      match status, ctx2.symbols.find? var with
      | .var v1, some (.var v2) =>
        some (.var ⟨v1.type, v1.initialised && v2.initialised⟩)
      | _, none => none
      | _, _    => some status
  let symbols := ctx1.symbols.filterMap intersect
  let strings := ctx1.strings ∪ ctx2.strings
  { name     := ctx1.name
  , symbols  := symbols
  , structs  := ctx1.structs
  , calls    := calls
  , strings  := strings
  , ret_type := ctx1.ret_type
  , returns  := returns
  }

structure Error.TExpr where
  Δ : Tst.GCtx
  Γ : Tst.FCtx
  τ : Typ
  e : Tst.Expr Δ Γ τ

structure Error where
  message : String
  expression : Option ((Ast.Expr ⊕ Error.TExpr) ⊕ Ast.LValue)
  statement : Option Ast.Stmt
  function : Option Symbol
deriving Inhabited

namespace Error

@[inline] def func (name : Symbol) (message : String) : Error :=
  ⟨message, none, none, some name⟩

@[inline] def stmt (stmt : Ast.Stmt) (message : String) : Error :=
  ⟨message, none, some stmt, none⟩

@[inline] def expr (expr : Ast.Expr) (message : String) : Error :=
  ⟨message, some (.inl <| .inl expr), none, none⟩
@[inline] def texpr (expr : Tst.Expr Δ Γ τ) (message : String) : Error :=
  ⟨message, some (.inl <| .inr ⟨Δ, Γ, τ, expr⟩), none, none⟩

@[inline] def no_contract
    (texpr : Tst.Expr Δ Γ τ)
    (_np : ¬(Tst.Expr.no_contract texpr))
    : Error :=
  Error.texpr texpr <| "Expression can only occur in contracts"

@[inline] def no_result
    (texpr : Tst.Expr Δ Γ τ)
    (_np : ¬(Tst.Expr.no_result texpr))
    : Error :=
  Error.texpr texpr <| "Result expression can only occur in ensures clauses"

@[inline] def lval (lv : Ast.LValue) (message : String) : Error :=
  ⟨message, some (.inr lv), none, none⟩

@[inline] def msg (message : String) : Error :=
  ⟨message, none, none, none⟩

def toString (err : Error) : String :=
  let funcMsg :=
    match err.function with
    | some f => s!" in function '{f}'"
    | none => ""
  let eMsg :=
    match err.expression with
    | some (.inl <| .inr d) => s!"in expression {d.e} with type {d.τ}\n  "
    | some (.inl <| .inl e) => s!"in expression {e}\n  "
    | some (.inr lv)        => s!"in lvalue {lv}\n  "
    | none                  => s!""
  let sMsg :=
    match err.statement with
    | some s => s!"at statement '{s.toPrettyString}'\n  "
    | none => s!""
  s!"Type error occurred{funcMsg}\n  {sMsg}{eMsg}  {err.message}"

instance : ToString Error := ⟨Error.toString⟩

end Error
