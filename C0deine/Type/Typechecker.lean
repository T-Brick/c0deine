import Std
import C0deine.Parser.Ast
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
  type : Typ
  initialised : Bool

structure Status.Func where
  type : FuncType
  defined : Bool

structure Status.Struct where
  fields : Symbol.Map Typ
  defined : Bool

inductive Status.Symbol
| var (v : Status.Var)
| func (f : Status.Func)
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

structure Error where
  message : String
  expression : Option ((Ast.Expr ⊕ (Typ.Typed Tst.Expr)) ⊕ Ast.LValue)
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
@[inline] def texpr (expr : Typ.Typed Tst.Expr) (message : String) : Error :=
  ⟨message, some (.inl <| .inr expr), none, none⟩

@[inline] def no_contract
    (texpr : Typ.Typed Tst.Expr)
    (_np : ¬(Tst.Expr.no_contract texpr.data))
    : Error :=
  Error.texpr texpr <| "Expression can only occur in contracts"

@[inline] def no_result
    (texpr : Typ.Typed Tst.Expr)
    (_np : ¬(Tst.Expr.no_result texpr.data))
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
    | some (.inl <| .inr e) => s!"in expression {e.data} with type {e.type}\n  "
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


def Trans.type [Ctx α] (ctx : α) : Ast.Typ → Option Typ
  | .int    => some <| .prim .int
  | .bool   => some <| .prim .bool
  | .char   => some <| .prim .char
  | .string => some <| .prim .string
  | .tydef name =>
    match (Ctx.symbols ctx).find? name with
    | some (.alias tau) => some tau
    | _ => none
  | .ptr (tau : Ast.Typ) => Trans.type ctx tau |>.map (.mem ∘ .pointer)
  | .arr (tau : Ast.Typ) => Trans.type ctx tau |>.map (.mem ∘ .array)
  | .struct name => some <| .mem (.struct name)

def Trans.isSized [Ctx α] (ctx : α) : Typ → Bool
  | .mem (.struct name) =>
    match (Ctx.structs ctx).find? name with
    | some status => status.defined
    | none => false
  | _ => true

def Trans.int_binop : Ast.BinOp.Int → Tst.BinOp.Int
  | .plus  => .plus
  | .minus => .minus
  | .times => .times
  | .div   => .div
  | .mod   => .mod
  | .and   => .and
  | .xor   => .xor
  | .or    => .or
  | .lsh   => .lsh
  | .rsh   => .rsh

def Trans.binop : Ast.BinOp → Tst.BinOp
  | .int op             => .int (Trans.int_binop op)
  | .bool .and          => .bool .and
  | .bool .or           => .bool .or
  | .cmp .less          => .cmp .less
  | .cmp .greater       => .cmp .greater
  | .cmp .equal         => .cmp .equal
  | .cmp .not_equal     => .cmp .not_equal
  | .cmp .less_equal    => .cmp .less_equal
  | .cmp .greater_equal => .cmp .greater_equal

def Trans.params (ctx : FuncCtx)
                 (params : List Ast.Param)
                 : Except Error (List Typ) :=
  params.foldrM (fun p acc =>
    match Trans.type ctx p.type with
    | some ty => pure (ty :: acc)
    | none => throw <| Error.msg s!"Function input must have declared type"
  ) []


def Validate.global_var (ctx : GlobalCtx)
                        (var : Symbol)
                        (tau : Typ)
                        (initialised : Bool)
                        : Except Error GlobalCtx := do
  if ¬Typ.isSmall tau
  then throw <| Error.msg s!"Variable '{var}' must have a small type"
  else
    match ctx.symbols.find? var with
    | some (.var _) => throw <| Error.msg s!"Variable '{var}' is declared twice"
    | some (.alias _) =>
      throw <| Error.msg <|
        s!"Variable '{var}' is declared but also used as a type alias"
    | some (.func _) | none => -- allow shadowing of func declaration
      let symbols' := ctx.symbols.insert var (.var ⟨tau, initialised⟩)
      return  { ctx with symbols := symbols' }

def Validate.var (ctx : FuncCtx)
                 (var : Symbol)
                 (tau : Typ)
                 (initialised : Bool)
                 : Except Error FuncCtx := do
  let ctx' := FuncCtx.toGlobalCtx ctx
  let gctx ← Validate.global_var ctx' var tau initialised
  return { ctx with symbols := gctx.symbols }

def Validate.typedef (ctx : GlobalCtx)
                     (var : Symbol)
                     (tau : Typ)
                     : Except Error GlobalCtx := do
  if ctx.symbols.contains var
  then throw <| Error.msg s!"Name for typedef '{var}' already used"
  else return {ctx with symbols := ctx.symbols.insert var (.alias tau)}

def Validate.fields (ctx : GlobalCtx)
                    (fields : List Ast.Field)
                    : Except Error (List (Symbol × Typ)) :=
  fields.foldrM (fun field acc => do
    if acc.any (fun (f', _tau') => field.name == f')
    then throw <| Error.msg <|
      s!"Struct field '{field.name}' appeared more than once"
    else
      let tau ←
        match Trans.type ctx field.type |>.filter (Trans.isSized ctx) with
        | some tau => pure tau
        | none => throw <| Error.msg <|
          s!"Struct field '{field.name}' must have a known type size"
      pure ((field.name, tau) :: acc)
  ) []

def Validate.params (ctx : FuncCtx)
                    (params : List Ast.Param)
                    : Except Error FuncCtx :=
  params.foldlM (fun ctx param =>
    match Trans.type ctx param.type with
    | none     => throw <| Error.msg <|
      s!"Function paramter must have a known type"
    | some tau => Validate.var ctx param.name tau true
  ) ctx

-- does not add function to the global context!
def Validate.func (ctx : GlobalCtx)
                  (extern : Bool)
                  (defining : Bool)
                  (name : Symbol)
                  (inputs : List Ast.Param)
                  (output : Option Typ)
                  : Except Error (Status.Symbol × FuncCtx) := do
  let fctx := GlobalCtx.toFuncCtx name output ctx
  let intypes ← Trans.params fctx inputs
  let status := .func ⟨⟨output, intypes⟩, extern || defining⟩
  let symbols' := fctx.symbols.insert name status
  let fctx ← Validate.params {fctx with symbols := symbols'} inputs
  if ¬(output.all Typ.isSmall)
  then throw <| Error.func name <|
    s!"Function has non-small output type '{output}'"
  else
    match ctx.symbols.find? name with
    | some (.var _var) =>
      throw <| Error.func name s!"Function name is already used as a variable"
    | some (.func f) =>
      if ¬extern && defining && f.defined
      then throw <| Error.func name s!"Function cannot be redefined"
      else if intypes ≠ f.type.args
      then throw <| Error.func name <|
        s!"Function inputs don't match prior declarations\n  Previously: {f.type.args}\n  Here: {intypes}"
      else if output ≠ f.type.ret
      then throw <| Error.func name <|
        s!"Function return type differs from prior declarations\n  Previously: {f.type.ret}\n  Here: {output}"
      else return (status, fctx)
    | some (.alias _type) =>
      throw <| Error.func name <| s!"Identifier is already used as a type"
    | _ => return (status, fctx)

def Validate.callsDefined (ctx : GlobalCtx)
                          (main : Symbol)
                          : Except Error Unit :=
  let err := fun name => throw <| Error.msg <|
    s!"Function '{name}' is called but not defined"
  ctx.calls.foldM (fun () name _ => do
    match ctx.symbols.find? name with
    | some (.func status) =>
      if status.defined
      then return ()
      else if name = main
      then throw <| Error.msg s!"Function 'main' must be defined"
      else err name
    | _ => err name
  ) ()

namespace Synth.Expr

structure Result (P : Tst.Expr → Bool) where
  calls   : Tst.Calls
  strings : List String
  texpr   : Typ.Typed Tst.Expr
  valid   : Tst.Expr.All P texpr.data

structure Result.List (P : Tst.Expr → Bool) where
  calls   : Tst.Calls
  strings : List String
  texprs  : List (Typ.Typed Tst.Expr)
  valid   : ∀ te ∈ texprs, Tst.Expr.All P te.data

@[inline] def ExprOutput (P : Tst.Expr → Bool) :=
  Except Error (Result P)

-- todo: types must be equivalent
def intersect_type (t1 : Typ) (t2 : Typ) : Typ :=
  match t1, t2 with
  | .mem (.pointer t1'), .mem (.pointer t2') =>
    (.mem ∘ .pointer) (intersect_type t1' t2')
  | .mem (.array t1'), .mem (.array t2') =>
    (.mem ∘ .array) (intersect_type t1' t2')
  | .any, _ => t2
  | _, .any => t1
  | _, _    => t1

def binop_type
    (expect₁ : Typ)
    (opt_expect₂ : Option Typ)
    (expr : Ast.Expr)
    (op : Ast.BinOp)
    (lhs : Typ)
    (rhs : Typ)
    : Except Error Typ := do
  let check := fun (ty : Typ) =>
    if expect₁ = ty then pure ty else
    match opt_expect₂ with
    | .some expect₂ =>
      if expect₂ = ty then pure ty else
      throw <| Error.expr expr <|
        s!"Binary operator '{op}' expects both sides to have type '{expect₁}' or '{expect₂}' but they both have type '{ty}'"
    | .none =>
      throw <| Error.expr expr <|
        s!"Binary operator '{op}' expects both sides to have type '{expect₁}' but they both have type '{ty}'"
  match lhs, rhs with
  | .prim .int, .prim .int    => check (.prim .int)
  | .prim .bool, .prim .bool  => check (.prim .bool)
  | .prim .char, .prim .char  => check (.prim .char)
  | .any, .any                => pure expect₁
  | _, _ => throw <| Error.expr expr <|
    if lhs.equiv rhs then
      s!"Binary operator '{op}' cannot operate on type '{lhs}'"
    else
      s!"Binary operator '{op}' expects both sides to have the same type but instead got '{lhs}' and '{rhs}'"

@[inline] def nonvoid (eres : ExprOutput P) : ExprOutput P := do
  let res ← eres
  match res.texpr.type with
  | .any => throw <| Error.texpr res.texpr <| s!"Expression cannot be void"
  | _ => return res

@[inline] def small (eres : ExprOutput P) : ExprOutput P := do
  let res ← eres
  if res.texpr.type.isSmall then return res
  else throw <| Error.texpr res.texpr <| s!"Expression cannot have large type"

@[inline] def small_nonvoid (eres : ExprOutput P)
    : ExprOutput P := do
   let res ← nonvoid eres
   if res.texpr.type.isSmall then return res
   else throw <| Error.texpr res.texpr <| s!"Expression cannot have large type"

mutual
def expr (ctx : FuncCtx)
    (P : Tst.Expr → Bool)
    (fail : (te : Typ.Typed Tst.Expr) → ¬P te.data → Error)
    (exp : Ast.Expr)
    : ExprOutput P := do
  match exp with
  | .num n             =>
    if p : P (.num n)
    then return ⟨ctx.calls, ctx.strings, ⟨.prim .int, .num n⟩, .num p⟩
    else throw <| fail ⟨.prim .int, .num n⟩ p
  | .char c            =>
    if p : P (.char c)
    then return ⟨ctx.calls, ctx.strings, ⟨.prim .char, .char c⟩, .char p⟩
    else throw <| fail ⟨.prim .char, .char c⟩ p
  | .str s             =>
    let strings' := if s ∉ ctx.strings then s::ctx.strings else ctx.strings
    if p : P (.str s)
    then return ⟨ctx.calls, strings', ⟨.prim .string, .str s⟩, .str p⟩
    else throw <| fail ⟨.prim .string, .str s⟩ p
  | .true              =>
    if p : P .true
    then return ⟨ctx.calls, ctx.strings, ⟨.prim .bool, .true⟩, .true p⟩
    else throw <| fail ⟨.prim .bool, .true⟩ p
  | .false             =>
    if p : P .false
    then return ⟨ctx.calls, ctx.strings, ⟨.prim .bool, .«false»⟩, .false p⟩
    else throw <| fail ⟨.prim .bool, .false⟩ p
  | .null              =>
    if p : P .null
    then return ⟨ctx.calls, ctx.strings, ⟨.mem (.pointer .any), .null⟩, .null p⟩
    else throw <| fail ⟨.mem (.pointer .any), .null⟩ p
  | .unop op e         =>
    let res ← small_nonvoid <| expr ctx P fail e
    let (op', tau) ←
      match op, res.texpr.type with
      | .int .neg, .prim .int
      | .int .neg, .any         => pure (.int .neg, .prim .int)
      | .int .not, .prim .int
      | .int .not, .any         => pure (.int .not, .prim .int)
      | .bool .neg, .prim .bool
      | .bool .neg, .any        => pure (.bool .neg, .prim .bool)
      | .int .neg, _
      | .int .not, _ =>
        throw <| Error.expr exp <|
          s!"Unary operator '{op}' expects type '{Typ.prim .int}' but got '{res.texpr.type}'"
      | .bool .neg, _ =>
        throw <|  Error.expr exp <|
          s!"Unary operator '{op}' expects type '{Typ.prim .bool}' but got '{res.texpr.type}'"
    let e' := .unop op' res.texpr
    if p : P e'
    then return ⟨res.calls, res.strings, ⟨tau, e'⟩, .unop res.valid p⟩
    else throw <| fail ⟨tau, e'⟩ p

  | .binop op l r      =>
    let resl ← small_nonvoid <| expr ctx P fail l
    let resr ← small_nonvoid <| expr ctx P fail r
    let e' : Tst.Expr := .binop (Trans.binop op) resl.texpr resr.texpr
    let calls   := resl.calls.merge resr.calls
    let strings := resl.strings ∪ resr.strings
    let tau ←
      match op with
      | .int .plus
      | .int .minus
      | .int .times
      | .int .div
      | .int .mod
      | .int .and
      | .int .xor
      | .int .or
      | .int .lsh
      | .int .rsh           =>
        binop_type (.prim .int) .none exp op resl.texpr.type resl.texpr.type

      | .cmp .less
      | .cmp .greater
      | .cmp .less_equal
      | .cmp .greater_equal =>
        let _ ← binop_type (.prim .int) (.some (.prim .char)) exp op
            resl.texpr.type resl.texpr.type
        pure (.prim .bool)

      | .bool .and
      | .bool .or           =>
        binop_type (.prim .bool) .none exp op resl.texpr.type resl.texpr.type

      | .cmp .equal
      | .cmp .not_equal     =>
        if resl.texpr.type.equiv resr.texpr.type then
          match resl.texpr.type with
          | .prim .string    => throw <| Error.expr exp <|
            s!"Binary operator '{op}' cannot compare strings."
          | .mem (.struct _) => throw <| Error.expr exp <|
            s!"Binary operator '{op}' cannot compare structs."
          | _                => pure (.prim .bool)
        else throw <| Error.expr exp <|
           s!"Binary operator '{op}' expects both sides to have same type but got '{resl.texpr.type}' and '{resr.texpr.type}'"
    if p : P e'
    then return ⟨calls, strings, ⟨tau, e'⟩, .binop resl.valid resr.valid p⟩
    else throw <| fail ⟨tau, e'⟩ p

  | .ternop cond tt ff =>
    let resc ← small_nonvoid <| expr ctx P fail cond
    let rest ← small_nonvoid <| expr ctx P fail tt
    let resf ← small_nonvoid <| expr ctx P fail ff
    let calls   := resc.calls.merge rest.calls |>.merge resf.calls
    let strings := resc.strings ∪ rest.strings ∪ resf.strings
    if resc.texpr.type ≠ .prim .bool
    then throw <| Error.expr exp s!"Ternary condition {resc.texpr} must be a bool"
    else if rest.texpr.type.equiv resf.texpr.type then
      let tau' := intersect_type rest.texpr.type resf.texpr.type
      let e'   := .ternop resc.texpr rest.texpr resf.texpr
      if p : P e' then
        return ⟨ calls
               , strings, ⟨tau', e'⟩
               , .ternop resc.valid rest.valid resf.valid p
               ⟩
      else throw <| fail ⟨tau', e'⟩ p
    else throw <| Error.expr exp <|
      s!"Ternary true branch has type '{rest.texpr.type}' but the false branch has type '{resf.texpr.type}'"

  | .app f args        =>
    match ctx.symbols.find? f with
    | some (.func status) =>
      let resargs ← exprs ctx P fail args
      let arg_types := resargs.texprs.map (fun arg => arg.type)
      let ret_type := -- return unit (i.e. void_star) if there's no return type
        match status.type.ret with
        | some tau => tau
        | none => .any
      let types_match := arg_types.zip status.type.args
        |>.all fun (a, b) => Typ.equiv a b
      if arg_types.length = status.type.args.length && types_match then
        let calls   := resargs.calls.insert f .false
        let e' := .app f resargs.texprs
        if p : P e' then
          return ⟨calls, resargs.strings, ⟨ret_type, e'⟩, .app resargs.valid p⟩
        else throw <| fail ⟨ret_type, e'⟩ p
      else throw <| Error.expr exp <|
        s!"Arguments should have types {status.type.args} but received {arg_types}"
    | some (.var _) => throw <| Error.expr exp <|
      s!"Cannot call variable {f} (non-function type)"
    | some (.alias _) => throw <| Error.expr exp s!"Cannot call type {f}"
    | none => throw <| Error.expr exp <|
      s!"Cannot call undeclared/undefined function {f}"

  | .alloc tau         =>
    let opt_tau' := Trans.type ctx tau |>.filter (Trans.isSized ctx)
    match opt_tau' with
    | some tau' =>
      let e' := .alloc tau'
      if p : P e'
      then return ⟨ctx.calls, ctx.strings, ⟨.mem (.pointer tau'), e'⟩, .alloc p⟩
      else throw <| fail ⟨.mem (.pointer tau'), e'⟩ p
    | none      => throw <| Error.expr exp s!"Invalid allocation type"

  | .alloc_array tau e =>
    let opt_tau' := Trans.type ctx tau |>.filter (Trans.isSized ctx)
    let res ← small_nonvoid <| expr ctx P fail e
    match opt_tau', res.texpr.type with
    | none, _ => throw <| Error.expr exp s!"Invalid array type"
    | some tau', .prim .int =>
      let e' := .alloc_array tau' res.texpr
      if p : P e' then
        return ⟨ res.calls
               , res.strings
               , ⟨.mem (.array tau'), e'⟩
               , .alloc_array res.valid p
               ⟩
      else throw <| fail ⟨.mem (.array tau'), e'⟩ p
    | _, _ => throw <| Error.expr exp <|
      s!"Array length expected an '{Typ.prim .int}' but got '{res.texpr.type}'"

  | .var name          =>
    match ctx.symbols.find? name with
    | some (.var status) =>
      if status.initialised then
        let e' := .var name
        if p : P e'
        then return ⟨ctx.calls, ctx.strings, ⟨status.type, e'⟩, .var p⟩
        else throw <| fail ⟨status.type, e'⟩ p
      else throw <| Error.expr exp s!"Variable not initialised"
    | _ => throw <| Error.expr exp s!"Variable not declared"

  | .dot e field       =>
    let res ← nonvoid <| expr ctx P fail e
    match res.texpr.type with
    | .mem (.struct name) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.texpr res.texpr s!"Struct '{name}' is not defined"
        else
          match status.fields.find? field with
          | some tau =>
            let e' := .dot res.texpr field
            if p : P e'
            then return ⟨res.calls, res.strings, ⟨tau, e'⟩, .dot res.valid p⟩
            else throw <| fail ⟨tau, e'⟩ p
          | none => throw <| Error.expr exp <|
            s!"Invalid field '{field}' for struct type '{res.texpr.type}'"
      | none => throw <| Error.texpr res.texpr s!"Struct '{name}' is not defined"
    | _ => throw <| Error.expr exp <|
      s!"Field accessor expects a struct not type '{res.texpr.type}'"

  | .arrow e field     =>
    let res ← expr ctx P fail e
    match res.texpr.type with
    | .mem (.pointer <| .mem (.struct name)) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.texpr res.texpr s!"Struct '{name}' is not defined"
        else if pe : P (.deref res.texpr) then
          let te' := ⟨.mem (.struct name), .deref res.texpr⟩
          have pe' : Tst.Expr.All P (Typ.Typed.data te') := by
            simp [Typ.Typed.data]
            exact .deref res.valid pe

          match status.fields.find? field with
          | some tau =>
            let e' := .dot te' field
            if p : P e'
            then return ⟨res.calls, res.strings, ⟨tau, e'⟩, .dot pe' p⟩
            else throw <| fail ⟨tau, e'⟩ p
          | none => throw <| Error.expr exp <|
            s!"Invalid field '{field}' for struct type '{te'.type}'"
        else throw <| fail ⟨.mem (.struct name), .deref res.texpr⟩ pe
      | none => throw <| Error.texpr res.texpr s!"Struct '{name}' is not defined"
    | _ => throw <| Error.expr exp <|
      s!"Arrow operator expects a struct pointer not type '{res.texpr.type}'"

  | .deref e           =>
    let res ← small <| expr ctx P fail e
    match res.texpr.type with
    | .mem (.pointer .any) => throw <| Error.expr e <|
      s!"Cannot dereference a null pointer"
    | .mem (.pointer tau)  =>
      let e' := .deref res.texpr
      if p : P e'
      then return ⟨res.calls, res.strings, ⟨tau, e'⟩, .deref res.valid p⟩
      else throw <| fail ⟨tau, e'⟩ p
    | _ => throw <| Error.expr e <|
      s!"Cannot dereference a non-pointer type '{res.texpr.type}'"

  | .index arr indx    =>
    let resa ← small_nonvoid <| expr ctx P fail arr
    let resi ← small_nonvoid <| expr ctx P fail indx
    let calls   := resa.calls.merge resi.calls
    let strings := resa.strings ∪ resi.strings
    match resa.texpr.type, resi.texpr.type with
    | .mem (.array tau), .prim .int =>
      let e' := .index resa.texpr resi.texpr
      if p : P e'
      then return ⟨calls, strings, ⟨tau, e'⟩, .index resa.valid resi.valid p⟩
      else throw <| fail ⟨tau, e'⟩ p
    | .mem (.array _tau), _ => throw <| Error.expr exp <|
      s!"Array indices must be type '{Typ.prim .int}' not type '{resi.texpr.type}'"
    | _, _ => throw <| Error.expr exp <|
      s!"Array indexing must be on array types not type '{resa.texpr.type}'"
  | .result           =>
    if p : P .result then
      match ctx.ret_type with
      | .some tau => return ⟨ctx.calls, ctx.strings, ⟨tau, .result⟩, .result p⟩
      | .none     => throw <| Error.expr exp <|
        s!"Cannot use result when function's return type is void"
    else throw <| fail ⟨.prim .int, .result⟩ p
  | .length e         =>
    let res ← small_nonvoid <| expr ctx P fail e
    match res.texpr.type with
    | .mem (.array _tau) =>
      let e' := .length res.texpr
      if p : P e' then
        return ⟨res.calls, res.strings, ⟨.prim .int, e'⟩, .length res.valid p⟩
      else throw <| fail ⟨.prim .int, e'⟩ p
    | _                 => throw <| Error.expr exp <|
      s!"Can only check the length of arrays not of type '{res.texpr.type}'"

def exprs (ctx : FuncCtx)
          (P : Tst.Expr → Bool)
          (fail : (te : Typ.Typed Tst.Expr) → ¬P te.data → Error)
          (exps : List Ast.Expr)
          : Except Error (Result.List P) := do
  match exps with
  | [] => return ⟨ctx.calls, ctx.strings, [], by simp⟩
  | e :: es =>
    let rese ← small_nonvoid <| expr ctx P fail e
    let reses ← exprs ctx P fail es
    let calls   := rese.calls.merge reses.calls
    let strings := rese.strings ∪ reses.strings
    return ⟨ calls
           , strings
           , rese.texpr :: reses.texprs
           , by simp; exact And.intro rese.valid reses.valid
           ⟩
end
termination_by
  expr ctx _ _ e   => sizeOf e
  exprs ctx _ _ es => sizeOf es

end Synth.Expr

namespace Synth.LValue

def Result := Except Error (Tst.Calls × Typ.Typed Tst.LValue)
deriving Inhabited

def small (res : Result) : Result := do
  let (calls, tv) ← res
  if tv.type.isSmall
  then return (calls, tv)
  else throw <| Error.msg s!"LValue has large type"

def lvalue (ctx : FuncCtx) (lval : Ast.LValue) : Result := do
  match lval with
  | .var var =>
    match ctx.symbols.find? var with
    | some (.var status) =>
      if status.initialised
      then return (ctx.calls, ⟨status.type, .var var⟩)
      else throw <| Error.lval lval s!"Variable not initialised"
    | _ => throw <| Error.lval lval s!"Variable not declared"

  | .dot lv field =>
    let (calls, lv') ← lvalue ctx lv
    match lv'.type with
    | .mem (.struct name) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.lval lval s!"Struct '{name}' is not defined"
        else
          match status.fields.find? field with
          | some tau => return (calls, ⟨tau, .dot lv' field⟩)
          | none => throw <| Error.lval lval <|
            s!"Invalid field '{field}' for struct type '{lv'.type}'"
      | none => throw <| Error.lval lval s!"Struct {name} is not defined"
    | _ => throw <| Error.lval lval <|
      s!"Field accessor expects a struct not type '{lv'.type}'"

  | .arrow lv field =>
    let (calls, lv') ← lvalue ctx lv
    match lv'.type with
    | .mem (.pointer <| .mem (.struct name)) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.lval lval s!"Struct '{name}' is not defined"
        else
          match status.fields.find? field with
          | some tau =>
            let struct := ⟨.mem (.struct name), .deref lv'⟩
            return (calls, ⟨tau, .dot struct field⟩)
          | none => throw <| Error.lval lval <|
            s!"Invalid field '{field}' for struct type '{lv'.type}'"
      | none => throw <| Error.lval lval s!"Struct '{name}' is not defined"
    | _ => throw <| Error.lval lval <|
      s!"Arrow operator expects a struct pointer not type '{lv'.type}'"

  | .deref lv =>
    let (calls, lv') ← lvalue ctx lv
    match lv'.type with
    | .mem (.pointer tau)  => return (calls, ⟨tau, .deref lv'⟩)
    | _ => throw <| Error.lval lval <|
      s!"Cannot dereference a non-pointer type '{lv'.type}'"

  | .index arr indx =>
    let (ca, arr') ← lvalue ctx arr
    let resi ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract indx
    let calls := ca.merge resi.calls
    match arr'.type, resi.texpr.type with
    | .mem (.array tau), .prim .int =>
      let indx' := ⟨resi.texpr.type, ⟨resi.texpr.data, resi.valid⟩⟩
      return (calls, ⟨tau, .index arr' indx'⟩)
    | .mem (.array _tau), _ => throw <| Error.lval lval <|
      s!"Array indices must be type '{Typ.prim .int}' not type '{resi.texpr.type}'"
    | _, _ => throw <| Error.lval lval <|
      s!"Array indexing must be on array types not type '{arr'.type}'"

end Synth.LValue

namespace Synth.Anno

def func (ctx : FuncCtx) (as : List Ast.Anno)
    : Except Error (FuncCtx × List Tst.Anno.Function) := do
  match as with
  | []                  => return (ctx, [])
  | .requires e :: rest =>
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_result Error.no_result e
    if res.texpr.type ≠ .prim .bool then
      throw <| Error.expr e <|
        s!"Requires must have type {Typ.prim .bool} not type '{res.texpr.type}'"
    else
      let calls' := ctx.calls.merge (res.calls.mapVal (fun _ _ => true))
      let (ctx', rest') ← func {ctx with calls := calls'} rest
      let e' := ⟨res.texpr.type, ⟨res.texpr.data, res.valid⟩⟩
      return ⟨ctx', ⟨.requires e', by simp⟩ :: rest'⟩

  | .ensures  e :: rest =>
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx (fun _ => true) (fun _ np => by simp at np) e
    if res.texpr.type ≠ .prim .bool then
      throw <| Error.expr e <|
        s!"Ensures must have type {Typ.prim .bool} not type '{res.texpr.type}'"
    else
      let calls' := ctx.calls.merge (res.calls.mapVal (fun _ _ => true))
      let (ctx', rest') ← func {ctx with calls := calls'} rest
      return ⟨ctx', ⟨.ensures res.texpr, by simp⟩ :: rest'⟩

  | .loop_invar _ :: _ =>
    throw <| Error.msg "Loop invariants can only precede loop bodies"
  | .assert _ :: _ =>
    throw <| Error.msg "Assert cannot annotate functions"

def loop (ctx : FuncCtx) (as : List Ast.Anno)
    : Except Error (FuncCtx × List Tst.Anno.Loop) := do
  match as with
  | []            => return (ctx, [])
  | .requires _   :: _    => throw <| Error.msg "Requires can only annotate functions"
  | .ensures  _   :: _    => throw <| Error.msg "Ensures can only annotate functions"
  | .loop_invar e :: rest =>
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_result Error.no_result e
    if res.texpr.type ≠ .prim .bool then
      throw <| Error.expr e <|
        s!"Loop invariants must have type {Typ.prim .bool} not type '{res.texpr.type}'"
    else
      let calls' := ctx.calls.merge (res.calls.mapVal (fun _ _ => true))
      let (ctx', rest') ← loop {ctx with calls := calls'} rest
      let e' := ⟨res.texpr.type, ⟨res.texpr.data, res.valid⟩⟩
      return (ctx', ⟨.loop_invar e', by simp⟩ :: rest')

  | .assert _ :: _       => throw <| Error.msg "Assert cannot annotate loops"

def free (ctx : FuncCtx) (a : Ast.Anno)
    : Except Error (FuncCtx × Tst.Anno.Free) := do
  match a with
  | .requires _   => throw <| Error.msg "Requires can only annotate functions"
  | .ensures  _   => throw <| Error.msg "Ensures can only annotate functions"
  | .loop_invar _ =>
    throw <| Error.msg "Loop invariants can only precede loop bodies"
  | .assert e =>
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_result Error.no_result e
    if res.texpr.type ≠ .prim .bool then
      throw <| Error.expr e <|
        s!"Assert must have type {Typ.prim .bool} not type '{res.texpr.type}'"
    else
      let calls' := ctx.calls.merge (res.calls.mapVal (fun _ _ => true))
      return ⟨{ctx with calls := calls'},
        ⟨.assert ⟨res.texpr.type, ⟨res.texpr.data, res.valid⟩⟩, by simp⟩
      ⟩

end Synth.Anno

namespace Stmt

def Result := Except Error (FuncCtx × Tst.Stmt)
deriving Inhabited

def wrapError (stmt : Ast.Stmt)
              (res : Except Error α)
              : Except Error α :=
  res.tryCatch (fun err => throw {err with statement := some stmt})

mutual
def stmt (ctx : FuncCtx) (stm : Ast.Stmt) : Result := do
  let handle      := wrapError stm
  let handleLV    := wrapError stm
  let handleAnno  := wrapError stm
  let handleAnnos := wrapError stm
  let throwS      := throw ∘ Error.stmt stm

  match stm with
  | .decl type name init body =>
    -- todo: this is kinda a mess, probably could be refactored a little
    let opt_tau := Trans.type ctx type |>.filter (Trans.isSized ctx)
    match opt_tau with
    | none => throwS s!"Unknown declaration type"
    | some tau =>
      if ¬tau.isSmall
      then throwS s!"Declarations must have small types"
      else
        let ctx' ← Validate.var ctx name tau (init.isSome)
        let (calls, strings, init') ←
          match init with
          | none => pure (ctx.calls, ctx.strings, none)
          | some e =>
            let res ← handle <| Synth.Expr.small_nonvoid <|
              Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
            -- types must be equivalent on both sides
            if res.texpr.type.equiv tau then
              let init' : Typ.Typed Tst.Expr.NoContract :=
                ⟨res.texpr.type, ⟨res.texpr.data, res.valid⟩⟩
              let res_init :=
                (res.calls, res.strings, some init')
              -- if we are assigning something to struct type, must be defined
              match res.texpr.type with
              | .mem (.struct sname) =>
                match ctx.structs.find? sname with
                | some status =>
                  if status.defined
                  then pure res_init
                  else throw <| Error.stmt stm <|
                    s!"Expression '{res.texpr.data}' has undefined type '{res.texpr.type}'"
                | _ => throw <| Error.stmt stm <|
                  s!"Expression '{res.texpr.data}' has undefined/undeclared type '{res.texpr.type}'"
              | _ => pure res_init
            else throw <| Error.stmt stm <|
              s!"Variable '{name}' has mismatched types. Declaration expects '{tau}' but {res.texpr.data} has type '{res.texpr.type}'"
        let (ctx'', body') ←
          stmts {ctx' with calls := ctx.calls.merge calls
                         , strings := strings ∪ ctx.strings
                         } body
        let symbols' := -- restore old symbol status
          match ctx.symbols.find? name with
          | some status => ctx''.symbols.insert name status
          | none => ctx''.symbols.erase name
        let calledOldCtx := { ctx'' with symbols := symbols' }
        return (calledOldCtx, .decl ⟨tau, name⟩ init' body')

  | .assn lv op e =>
    match lv with
    | .var var =>
      let elab_e :=
        match op with
        | .eq => e
        | .aseq binop => .binop (.int binop) (.var var) e
      match ctx.symbols.find? var with
      | none => throwS s!"Variable '{var}' must be initialised before assignment"
      | some status =>
        match status with
        | .var vstatus =>
          let res ← handle <| Synth.Expr.small_nonvoid <|
              Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract elab_e
          let ctx := {ctx with calls := res.calls, strings := res.strings}
          if res.texpr.type.equiv vstatus.type
          then
            let ctx' :=
              match vstatus.initialised with
              | true  => ctx
              | false =>
                let symbols' :=
                  ctx.symbols.insert var (.var ⟨vstatus.type, true⟩)
                { ctx with symbols := symbols' }
            let e' := ⟨res.texpr.type, ⟨res.texpr.data, res.valid⟩⟩
            return (ctx', .assign ⟨res.texpr.type, .var var⟩ none e')
          else throwS s!"Assignment of '{var}' expects type '{vstatus.type}' but got '{res.texpr.type}'"
        | .func _  => throwS s!"Cannot assign to function '{var}'"
        | .alias _ => throwS s!"Cannot assign to type alias '{var}'"

    | _         =>
      let ⟨cl, l'⟩ ←
        handleLV <| Synth.LValue.small <| Synth.LValue.lvalue ctx lv
      let resr ← handle <| Synth.Expr.small_nonvoid <|
        Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
      let ctx := { ctx with calls := cl.merge resr.calls
                          , strings := resr.strings
                 }
      if l'.type.equiv resr.texpr.type then
        let e' := ⟨resr.texpr.type, ⟨resr.texpr.data, resr.valid⟩⟩
        match op with
        | .eq =>
          return (ctx, .assign l' none e')
        | .aseq binop =>
          if l'.type.equiv (.prim .int) then
            return (ctx, .assign l' (some (Trans.int_binop binop)) e')
          else throwS s!"Assignment with operations must have type '{Typ.prim .int}' not '{l'.type}'"
      else throwS s!"Left side of assignment has type '{l'.type}' doesn't match the right side '{resr.texpr.type}'"

  | .ite cond tt ff =>
    let resc ← handle <| Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract cond
    let ctx' := {ctx with calls := resc.calls, strings := resc.strings}
    match resc.texpr.type with
    | .prim .bool =>
      let (ctx1, tt') ← stmts ctx' tt
      let (ctx2, ff') ← stmts ctx' ff
      let cond' := ⟨resc.texpr.type, ⟨resc.texpr.data, resc.valid⟩⟩
      return (ctx1.join ctx2, .ite cond' tt' ff')
    | _ => throwS s!"If condition must be of type '{Typ.prim .bool}' not '{resc.texpr.type}'"

  | .while cond annos body =>
    let resc ← handle <| Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract cond
    let (ctx', annos') ← handleAnnos <| Synth.Anno.loop ctx annos
    match resc.texpr.type with
    | .prim .bool =>
      let (ctx'', body') ←
        stmts ctx' body
      let cond' := ⟨resc.texpr.type, ⟨resc.texpr.data, resc.valid⟩⟩
      let ctx''' :=
        { ctx with calls   := ctx''.calls.merge resc.calls
                 , strings := ctx''.strings ∪ resc.strings
        }
      return (ctx''', .while cond' annos' body')
    | _ => throwS s!"Loop condition must be of type '{Typ.prim .bool}' not '{resc.texpr.type}'"

  | .return eOpt =>
    let calls_eOpt' ←
      eOpt.mapM (
        handle ∘ Synth.Expr.small_nonvoid
               ∘ Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract
      )
    let eOpt' : Option (Typ.Typed Tst.Expr.NoContract) :=
      calls_eOpt'.map (fun res => ⟨res.texpr.type, ⟨res.texpr.data, res.valid⟩⟩)
    let calls   := calls_eOpt'.elim ctx.calls (·.calls)
    let strings := calls_eOpt'.elim ctx.strings (·.strings)
    let () ←
      match eOpt', ctx.ret_type with
      | none, none => pure ()
      | some e', some tau =>
        if e'.type.equiv tau
        then pure ()
        else throw <| Error.stmt stm <|
          s!"Expected return type was '{ctx.ret_type}' but got '{e'.type}'"
      | some e', _ =>
        throw <| Error.stmt stm <|
          s!"Expected return type was '{ctx.ret_type}' but got '{e'.type}'"
      | none, _ =>
        throw <| Error.stmt stm <|
          s!"Expected return type is '{ctx.ret_type}'"

    let symbols' := ctx.symbols.mapVal (fun _ status =>
        match status with
        | .var vstatus => Status.Symbol.var {vstatus with initialised := true}
        | _ => status
      )
    let ctx' := { ctx with symbols := symbols'
                         , calls   := calls
                         , strings := strings
                         , returns := true
                }
    return (ctx', .return eOpt')

  | .assert e =>
    let res ← handle <| Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
    match res.texpr.type with
    | .prim .bool =>
      let e'   := ⟨res.texpr.type, ⟨res.texpr.data, res.valid⟩⟩
      let ctx' := { ctx with calls := res.calls, strings := res.strings }
      return (ctx', .assert e')
    | _ => throwS s!"Assert condition must be of type '{Typ.prim .bool}' not '{res.texpr.type}'"

  | .error e =>
    let res ← handle <| Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
    match res.texpr.type with
    | .prim .string =>
      let e'   := ⟨res.texpr.type, ⟨res.texpr.data, res.valid⟩⟩

      /- Sets all variables to initialised. `cc0` does not have the behaviour
          but when outputing `c` code from `cc0`, `error` is elaborated to
          `exit`. The C standard defines `exit` to never return, and `gcc` does
          not warn about uninitialised variables after an `exit`, which
          indicates to me that this should be the behaviour.
      -/
      let symbols' := ctx.symbols.mapVal (fun _ status =>
        match status with
        | .var vstatus => Status.Symbol.var {vstatus with initialised := true}
        | _ => status
      )
      let ctx' := { ctx with symbols := symbols'
                           , calls   := res.calls
                           , strings := res.strings
                           , returns := true
                  }
      return (ctx', .error e')
    | _ => throwS s!"Error condition must be of type '{Typ.prim .string}' not '{res.texpr.type}'"

  | .exp e =>
    let res ← handle <| Synth.Expr.small <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
    let e'   := ⟨res.texpr.type, ⟨res.texpr.data, res.valid⟩⟩
    let ctx' := {ctx with calls := res.calls, strings := res.strings}
    return (ctx', .expr e')

  | .anno a =>
    let (ctx', a') ← handleAnno <| Synth.Anno.free ctx a
    return (ctx', .anno a')

def stmts (ctx : FuncCtx)
          (body : List Ast.Stmt)
          : Except Error (FuncCtx × List Tst.Stmt) := do
  match body with
  | [] => return (ctx, [])
  | b::bs =>
    let (ctx', b') ← stmt ctx b
    let (ctx'', bs') ← stmts ctx' bs
    return (ctx'', b' :: bs')
end
termination_by
  stmt ctx s   => sizeOf s
  stmts ctx ss => sizeOf ss

end Stmt

namespace Global

def Result := Except Error (GlobalCtx × Option Tst.GDecl)
deriving Inhabited

def func (ctx : GlobalCtx)
         (extern : Bool)
         (defining : Bool)
         (name : Ast.Ident)
         (ret : Option Ast.Typ)
         (params : List Ast.Param)
         : Except Error (GlobalCtx × FuncCtx × Option Typ) := do
  let ret' ← ret.mapM (fun ret =>
      match Trans.type ctx ret with
      | some ret' => pure ret'
      | none => throw <| Error.func name <|
        s!"Function must have a declared type"
    )

  let (status, fctx) ← Validate.func ctx extern defining name params ret'
  let status' ←
    match ctx.symbols.find? name with
    | some (.func f) =>
      if ¬extern && defining && f.defined
      then throw <| Error.func name <| s!"Function was already defined"
      else pure (.func {f with defined := extern || f.defined || defining})
    | some (.alias _) => throw <| Error.func name <|
      s!"Function name collides with type alias"
    | some (.var _) => throw <| Error.func name <| -- shouldn't happen
      s!"Function name collides with global variable"
    | none => pure status

  let symbols := ctx.symbols.insert name status'
  return ({ctx with symbols}, fctx, ret')

def fdecl (extern : Bool) (ctx : GlobalCtx) (f : Ast.FDecl) : Result := do
  if extern && Symbol.main == f.name
  then throw <| Error.func f.name <|
    s!"Function 'main' cannot appear in headers"
  else
    let (ctx', fctx, ret) ← func ctx extern false f.name f.type f.params
    let params ← Trans.params fctx f.params
    let (fctx', annos) ← Synth.Anno.func fctx f.annos
    let fdecl := .fdecl ⟨ret, f.name, params, annos⟩
    return ({ctx' with calls := ctx'.calls.merge fctx'.calls}, some fdecl)

def fdef (extern : Bool) (ctx : GlobalCtx) (f : Ast.FDef) : Result := do
  if extern
  then throw <| Error.func f.name <|
    s!"Function definitions cannot be in headers"
  else
    let (ctx', fctx, ret) ← func ctx extern true f.name f.type f.params
    let params : List (Typ.Typed Symbol) ← f.params.foldrM (fun p acc =>
        match Trans.type fctx p.type with
        | some ty => pure (⟨ty, p.name⟩ :: acc)
        | none => throw <| Error.func f.name <|
          s!"Function input must have non-void, declared type"
      ) []
    let (fctx', annos) ← Synth.Anno.func fctx f.annos
    let (fctx'', body') ←
      Stmt.stmts fctx' f.body |>.tryCatch
        (fun err => throw {err with function := some f.name})

    if ¬(ret.isNone || fctx''.returns)
    then throw <| Error.func f.name <|
        s!"Function does not return on some paths"

    let body'' :=
      if ret.isNone
      then body'.append [.return none]
      else body'

    let funcCalls := ctx'.funcCalls.insert f.name fctx''.calls
    let calls     := ctx'.calls.merge fctx''.calls
    let strings   := ctx'.strings ∪ fctx''.strings

    let fdef := .fdef ⟨ret, f.name, params, annos, body''⟩
    return ({ctx' with calls, funcCalls, strings}, some fdef)

def tydef (ctx : GlobalCtx) (t : Ast.TyDef) : Result := do
  let tau' ←
    match Trans.type ctx t.type with
    | some tau => pure tau
    | none => throw <| Error.msg <| s!"'{t}' must have a non-void, known type"
  let ctx' ← Validate.typedef ctx t.name tau'
  return (ctx', none)

def sdecl (ctx : GlobalCtx) (s : Ast.SDecl) : Result := do
  let structs' :=
    match ctx.structs.find? s.name with
    | none =>
      ctx.structs.insert s.name ⟨Std.HashMap.empty, false⟩
    | some _ => ctx.structs
  return ({ctx with structs := structs'}, none)

def sdef (ctx : GlobalCtx) (s : Ast.SDef) : Result := do
  let () ←
    match ctx.structs.find? s.name with
    | some status =>
      if status.defined
      then throw <| Error.msg <| s!"Struct {s.name} has already been defined"
      else pure ()
    | none => pure ()
  let fieldsMap ← Validate.fields ctx s.fields
  let status := ⟨Std.HashMap.ofList fieldsMap, true⟩
  let structs' := ctx.structs.insert s.name status
  let fields' := fieldsMap.map (fun (field, tau) => ⟨tau, field⟩)
  return ({ctx with structs := structs'}, some (.sdef ⟨s.name, fields'⟩))

def gdec (extern : Bool) (ctx : GlobalCtx) (g : Ast.GDecl) : Result := do
  match g with
  | .fdecl f => fdecl extern ctx f
  | .fdef  f => fdef extern ctx f
  | .tydef t => tydef ctx t
  | .sdecl s => sdecl ctx s
  | .sdef  s => sdef ctx s

end Global

def typecheck (prog : Ast.Prog) : Except Error Tst.Prog := do
  let main_info := .func ⟨⟨some (.prim .int), []⟩, false⟩
  let main_sym := Symbol.main

  let init_symbols := Std.HashMap.empty.insert main_sym main_info
  let init_calls := Std.HashMap.empty.insert main_sym false
  let init_context : GlobalCtx :=
    ⟨init_symbols, Std.HashMap.empty, init_calls, Std.HashMap.empty, []⟩

  let checkDec := fun extern (ctx, prog) g => do
    -- run through the program, carrying the global context
    let (ctx', gOpt) ← liftM <| Global.gdec extern ctx g
    match gOpt with
    | some g' => return (ctx', g' :: prog)
    | none => return (ctx', prog)

  prog.header.foldlM (m := Except Error) (checkDec true) (init_context, [])
  |>.bind (fun (ctx, hres) => do
    let (ctx', bres) ←
      prog.program.foldlM (m := Except Error) (checkDec false) (ctx, [])
    pure (ctx', hres, bres))
  |>.bind (fun (ctx, hres, bres) => do
    -- check the all called functions are defined
    let () ← Validate.callsDefined ctx main_sym
    -- program is reversed so flip it back
    return ⟨hres.reverse, bres.reverse, ctx.calls, ctx.strings.reverse⟩)
