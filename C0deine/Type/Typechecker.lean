import Std
import C0deine.Parser.Ast
import C0deine.Type.Typ
import C0deine.Type.Tst
import C0deine.Utils.Symbol
import C0deine.Utils.Comparison
import C0deine.Utils.Context

namespace C0deine.Typechecker

@[inline] def Typed := Tst.Typed

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
def Calls := Symbol.Map Unit

def Calls.merge (calls1 calls2 : Calls) : Calls :=
  calls1.mergeWith (fun _ () () => ()) calls2

class Ctx (α : Type) where
  symbols : α → SymbolTable
  structs : α → StructTable
  calls   : α → Calls

structure FuncCtx where
  name    : Symbol
  symbols : SymbolTable
  structs : StructTable
  calls   : Calls
  ret_type : Option Typ
  returns : Bool
instance : Ctx FuncCtx where
  symbols := FuncCtx.symbols
  structs := FuncCtx.structs
  calls   := FuncCtx.calls

structure GlobalCtx where
  symbols   : SymbolTable
  structs   : StructTable
  calls     : Calls
  funcCalls : Symbol.Map Calls

instance : Ctx GlobalCtx where
  symbols := GlobalCtx.symbols
  structs := GlobalCtx.structs
  calls   := GlobalCtx.calls


-- defaults to not returning
def GlobalCtx.toFuncCtx (name : Symbol)
                         (ret : Option Typ)
                         (ctx : GlobalCtx)
                         : FuncCtx :=
  ⟨name, ctx.symbols, ctx.structs, ctx.calls, ret, false⟩

def FuncCtx.toGlobalCtx (ctx : FuncCtx) : GlobalCtx :=
  ⟨ctx.symbols, ctx.structs, ctx.calls, Std.HashMap.empty.insert ctx.name ctx.calls⟩

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
  ⟨ctx1.name, symbols, ctx1.structs, calls, ctx1.ret_type, returns⟩

structure Error where
  message : String
  expression : Option ((Ast.Expr ⊕ (Tst.Typed Tst.Expr)) ⊕ Ast.LValue)
  statement : Option Ast.Stmt
  function : Option Symbol
deriving Inhabited

namespace Error

def func (name : Symbol) (message : String) : Error :=
  ⟨message, none, none, some name⟩

def stmt (stmt : Ast.Stmt) (message : String) : Error :=
  ⟨message, none, some stmt, none⟩

def expr (expr : Ast.Expr) (message : String) : Error :=
  ⟨message, some (.inl <| .inl expr), none, none⟩
def texpr (expr : Tst.Typed Tst.Expr) (message : String) : Error :=
  ⟨message, some (.inl <| .inr expr), none, none⟩

def lval (lv : Ast.LValue) (message : String) : Error :=
  ⟨message, some (.inr lv), none, none⟩

def msg (message : String) : Error :=
  ⟨message, none, none, none⟩

def toString (err : Error) : String :=
  let funcMsg :=
    match err.function with
    | some f => s!" in function '{f}'"
    | none => ""
  let eMsg :=
    match err.expression with
    | some (.inl <| .inr e) => s!"in expression {e.data} with type {e.typ}\n  "
    | some (.inl <| .inl e) => s!"in expression {e}\n  "
    | some (.inr lv)        => s!"in lvalue {lv}\n  "
    | none                  => ""
  let sMsg :=
    match err.statement with
    | some s => s!"at statement '{s.toPrettyString}'\n  "
    | none => ""
  s!"Type error occurred{funcMsg}\n  {sMsg}{eMsg}  {err.message}"

instance : ToString Error where toString := Error.toString

end Error


def Trans.type [Ctx α] (ctx : α) : Ast.Typ → Option Typ
  | .int => some <| .prim .int
  | .bool => some <| .prim .bool
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
    | none     => throw <| Error.msg "Function paramter must have a known type"
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
  ctx.calls.foldM (fun () name () => do
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

def Result := Except Error (Calls × Tst.Typed Tst.Expr)
deriving Inhabited

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

def binop_type (expect : Typ)
               (expr : Ast.Expr)
               (op : Ast.BinOp)
               (lhs : Typ)
               (rhs : Typ)
               : Except Error Typ := do
  let check := fun (ty : Typ) =>
    if expect = ty
    then pure ty
    else throw <| Error.expr expr <|
      s!"Binary operator '{op}' expects both sides to have type {expect} but they both have type '{ty}'"
  match lhs, rhs with
  | .prim .int, .prim .int    => check (.prim .int)
  | .prim .bool, .prim .bool  => check (.prim .bool)
  | .any, .any                => pure expect
  | _, _ => throw <| Error.expr expr <|
      s!"Binary operator '{op}' expects both sides to have the same type but instead got '{lhs}' and '{rhs}'"

def nonvoid (res : Result) : Result := do
  let (calls, te) ← res
  match te.typ with
  | .any => throw <| Error.texpr te <| s!"Expression cannot be void"
  | _ => return (calls, te)

def small (res : Result) : Result := do
  let (calls, te) ← res
  if te.typ.isSmall then return (calls, te)
  else throw <| Error.texpr te <| s!"Expression cannot have large type"

def small_nonvoid (res : Result) : Result := do
   let (calls, te) ← nonvoid res
   if te.typ.isSmall then return (calls, te)
   else throw <| Error.texpr te <| s!"Expression cannot have large type"

mutual
def expr (ctx : FuncCtx) (exp : Ast.Expr) : Result := do
  match exp with
  | .num n             =>
    return (ctx.calls, ⟨.prim .int, .num n⟩)
  | .«true»            =>
    return (ctx.calls, ⟨.prim .bool, .«true»⟩)
  | .«false»           =>
    return (ctx.calls, ⟨.prim .bool, .«false»⟩)
  | .null              =>
    return (ctx.calls, ⟨.mem (.pointer .any), .null⟩)
  | .unop op e         =>
    let (calls, te) ← small_nonvoid <| expr ctx e
    let (op', tau) ←
      match op, te.typ with
      | .int .neg, .prim .int
      | .int .neg, .any         => pure (.int .neg, .prim .int)
      | .int .not, .prim .int
      | .int .not, .any         => pure (.int .not, .prim .int)
      | .bool .neg, .prim .bool
      | .bool .neg, .any        => pure (.bool .neg, .prim .bool)
      | .int .neg, _
      | .int .not, _ =>
        throw <| Error.expr exp <|
          s!"Unary operator '{op}' expects type '{Typ.prim .int}' but got '{te.typ}'"
      | .bool .neg, _ =>
        throw <|  Error.expr exp <|
          s!"Unary operator '{op}' expects type '{Typ.prim .bool}' but got '{te.typ}'"
    return (calls, ⟨tau, .unop op' te⟩)

  | .binop op l r      =>
    let (cl, l') ← small_nonvoid <| expr ctx l
    let (cr, r') ← small_nonvoid <| expr ctx r
    let e' : Tst.Expr := .binop (Trans.binop op) l' r'
    let calls := cl.merge cr
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
      | .int .rsh           => binop_type (.prim .int) exp op l'.typ r'.typ
      | .cmp .less
      | .cmp .greater
      | .cmp .less_equal
      | .cmp .greater_equal =>
        let _ ← binop_type (.prim .int) exp op l'.typ r'.typ
        pure (.prim .bool)
      | .bool .and
      | .bool .or           => binop_type (.prim .bool) exp op l'.typ r'.typ
      | .cmp .equal
      | .cmp .not_equal     =>
        if l'.typ.equiv r'.typ
        then pure (.prim .bool)
        else throw <| Error.expr exp <|
           s!"Binary operator '{op}' expects both sides to have same type but got '{l'.typ}' and '{r'.typ}'"
    return (calls, ⟨tau, e'⟩)

  | .ternop cond tt ff =>
    let (cc, c') ← small_nonvoid <| expr ctx cond
    let (ct, tt') ← small_nonvoid <| expr ctx tt
    let (cf, ff') ← small_nonvoid <| expr ctx ff
    let calls := cc.merge ct |>.merge cf
    if c'.typ ≠ .prim .bool
    then throw <| Error.expr exp s!"Ternary condition {c'} must be a bool"
    else
      if tt'.typ.equiv ff'.typ
      then
        let tau' := intersect_type tt'.typ ff'.typ
        return (calls, ⟨tau', .ternop c' tt' ff'⟩)
      else throw <| Error.expr exp <|
        s!"Ternary true branch has type '{tt'.typ}' but the false branch has type '{ff'.typ}'"

  | .app f args        =>
    match ctx.symbols.find? f with
    | some (.func status) =>
      let (calls, args') ← exprs ctx args
      let arg_types := args'.map (fun arg => arg.typ)
      let ret_type := -- return unit (i.e. void_star) if there's no return type
        match status.type.ret with
        | some tau => tau
        | none => .any
      if arg_types.length = status.type.args.length
      && (List.zip arg_types status.type.args
          |>.all fun (a, b) => Typ.equiv a b)
      then return (calls.insert f (), ⟨ret_type, .app f args'⟩)
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
    | some tau' => return (ctx.calls, ⟨.mem (.pointer tau'), .alloc tau'⟩)
    | none      => throw <| Error.expr exp s!"Invalid allocation type"

  | .alloc_array tau e =>
    let opt_tau' := Trans.type ctx tau |>.filter (Trans.isSized ctx)
    let (calls, e') ← small_nonvoid <| expr ctx e
    match opt_tau', e'.typ with
    | none, _ => throw <| Error.expr exp s!"Invalid array type"
    | some tau', .prim .int =>
      return (calls, ⟨.mem (.array tau'), .alloc_array tau' e'⟩)
    | _, _ => throw <| Error.expr exp <|
      s!"Array length expected an '{Typ.prim .int}' but got '{e'.typ}'"

  | .var name          =>
    match ctx.symbols.find? name with
    | some (.var status) =>
      if status.initialised
      then return (ctx.calls, ⟨status.type, .var name⟩)
      else throw <| Error.expr exp s!"Variable not initialised"
    | _ => throw <| Error.expr exp s!"Variable not declared"

  | .dot e field       =>
    let (calls, e') ← nonvoid <| expr ctx e
    match e'.typ with
    | .mem (.struct name) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.texpr e' s!"Struct '{name}' is not defined"
        else
          match status.fields.find? field with
          | some tau => return (calls, ⟨tau, .dot e' field⟩)
          | none => throw <| Error.expr exp <|
            s!"Invalid field '{field}' for struct type '{e'.typ}'"
      | none => throw <| Error.texpr e' s!"Struct '{name}' is not defined"
    | _ => throw <| Error.expr exp <|
      s!"Field accessor expects a struct not type '{e'.typ}'"

  | .arrow e field     =>
    let (calls, e') ← expr ctx e
    match e'.typ with
    | .mem (.pointer <| .mem (.struct name)) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.texpr e' s!"Struct '{name}' is not defined"
        else
          match status.fields.find? field with
          | some tau => return (calls, ⟨tau, .dot e' field⟩)
          | none => throw <| Error.expr exp <|
            s!"Invalid field '{field}' for struct type '{e'.typ}'"
      | none => throw <| Error.texpr e' s!"Struct '{name}' is not defined"
    | _ => throw <| Error.expr exp <|
      s!"Arrow operator expects a struct pointer not type '{e'.typ}'"

  | .deref e           =>
    let (calls, e') ← small <| expr ctx e
    match e'.typ with
    | .mem (.pointer .any) => throw <| Error.expr e <|
      "Cannot dereference a null pointer"
    | .mem (.pointer tau)  => return (calls, ⟨tau, .deref e'⟩)
    | _ => throw <| Error.expr e <| "Cannot dereference a non-pointer type '{e'.typ}'"

  | .index arr indx    =>
    let (ca, arr') ← small_nonvoid <| expr ctx arr
    let (ci, index') ← small_nonvoid <| expr ctx indx
    let calls := ca.merge ci
    match arr'.typ, index'.typ with
    | .mem (.array tau), .prim .int =>
      return (calls, ⟨tau, .index arr' index'⟩)
    | .mem (.array _tau), _ => throw <| Error.expr exp <|
      "Array indices must be type '{Typ.prim .int}' not type '{index'.typ}'"
    | _, _ => throw <| Error.expr exp <|
      "Array indexing must be on array types not type '{arr'.typ}'"

def exprs (ctx : FuncCtx)
          (exps : List Ast.Expr)
          : Except Error (Calls × List (Typed Tst.Expr)) := do
  match exps with
  | [] => return (ctx.calls, [])
  | e :: es =>
    let (calls1, e') ← small_nonvoid <| expr ctx e
    let (calls, es') ← exprs ctx es
    return (calls1.merge calls, e' :: es')
end

termination_by
  expr ctx e   => sizeOf e
  exprs ctx es => sizeOf es

end Synth.Expr

namespace Synth.LValue

def Result := Except Error (Calls × Typed Tst.LValue)
deriving Inhabited

def small (res : Result) : Result := do
  let (calls, tv) ← res
  if tv.typ.isSmall
  then return (calls, tv)
  else throw <| Error.msg "LValue has large type"

def lvalue (ctx : FuncCtx) (lval : Ast.LValue) : Result := do
  match lval with
  | .var var =>
    match ctx.symbols.find? var with
    | some (.var status) =>
      if status.initialised
      then return (ctx.calls, ⟨status.type, .var var⟩)
      else throw <| Error.lval lval "Variable not initialised"
    | _ => throw <| Error.lval lval "Variable not declared"

  | .dot lv field =>
    let (calls, lv') ← lvalue ctx lv
    match lv'.typ with
    | .mem (.struct name) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.lval lval s!"Struct '{name}' is not defined"
        else
          match status.fields.find? field with
          | some tau => return (calls, ⟨tau, .dot lv' field⟩)
          | none => throw <| Error.lval lval <|
            s!"Invalid field '{field}' for struct type '{lv'.typ}'"
      | none => throw <| Error.lval lval s!"Struct {name} is not defined"
    | _ => throw <| Error.lval lval <|
      s!"Field accessor expects a struct not type '{lv'.typ}'"

  | .arrow lv field =>
    let (calls, lv') ← lvalue ctx lv
    match lv'.typ with
    | .mem (.pointer <| .mem (.struct name)) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.lval lval s!"Struct '{name}' is not defined"
        else
          match status.fields.find? field with
          | some tau => return (calls, ⟨tau, .dot lv' field⟩)
          | none => throw <| Error.lval lval <|
            s!"Invalid field '{field}' for struct type '{lv'.typ}'"
      | none => throw <| Error.lval lval s!"Struct '{name}' is not defined"
    | _ => throw <| Error.lval lval <|
      s!"Arrow operator expects a struct pointer not type '{lv'.typ}'"

  | .deref lv =>
    let (calls, lv') ← lvalue ctx lv
    match lv'.typ with
    | .mem (.pointer tau)  => return (calls, ⟨tau, .deref lv'⟩)
    | _ => throw <| Error.lval lval <| "Cannot dereference a non-pointer type '{lv'.typ}'"

  | .index arr indx =>
    let (ca, arr') ← lvalue ctx arr
    let (ci, index') ← Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx indx
    let calls := ca.merge ci
    match arr'.typ, index'.typ with
    | .mem (.array tau), .prim .int =>
      return (calls, ⟨tau, .index arr' index'⟩)
    | .mem (.array _tau), _ => throw <| Error.lval lval <|
      "Array indices must be type '{Typ.prim .int}' not type '{index'.typ}'"
    | _, _ => throw <| Error.lval lval <|
      "Array indexing must be on array types not type '{arr'.typ}'"

end Synth.LValue


namespace Stmt

def Result := Except Error (FuncCtx × Tst.Stmt)
deriving Inhabited

def wrapError (stmt : Ast.Stmt)
              (res : Except Error α)
              : Except Error α :=
  res.tryCatch (fun err => throw {err with statement := some stmt})

mutual
def stmt (ctx : FuncCtx) (stm : Ast.Stmt) : Result := do
  let handle := wrapError stm
  let handleLV := wrapError stm
  let throwS := throw ∘ Error.stmt stm

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
        let (calls, init') ←
          match init with
          | none => pure (ctx.calls, none)
          | some e =>
            let (calls, e') ← handle <|
              Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx e
            -- types must be equivalent on both sides
            if e'.typ.equiv tau
            then
              let res := (calls, some e')
              -- if we are assigning something to struct type, must be defined
              match e'.typ with
              | .mem (.struct sname) =>
                match ctx.structs.find? sname with
                | some status =>
                  if status.defined
                  then pure res
                  else throw <| Error.stmt stm <|
                    s!"Expression '{e'.data}' has undefined type '{e'.typ}'"
                | _ => throw <| Error.stmt stm <|
                  s!"Expression '{e'.data}' has undefined/undeclared type '{e'.typ}'"
              | _ => pure res
            else throw <| Error.stmt stm <|
              s!"Variable '{name}' has mismatched types. Declaration expects '{tau}' but {e'.data} has type '{e'.typ}'"
        let (ctx'', body') ← stmts {ctx' with calls} body
        let symbols' := -- restore old symbol status
          match ctx.symbols.find? name with
          | some status => ctx''.symbols.insert name status
          | none => ctx''.symbols.erase name
        let calledOldCtx := { ctx'' with symbols := symbols' }
        return (calledOldCtx, .decl ⟨tau, name⟩ init' body'.reverse)

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
          let (calls, e') ←
            handle <| Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx elab_e
          let ctx := {ctx with calls}
          if e'.typ.equiv vstatus.type
          then
            let ctx' :=
              match vstatus.initialised with
              | true  => ctx
              | false =>
                { ctx with
                    symbols := ctx.symbols.insert var (.var ⟨vstatus.type, true⟩)
                }
            return (ctx', .assign ⟨e'.typ, .var var⟩ none e')
          else throwS s!"Assignment of '{var}' expects type '{vstatus.type}' but got '{e'.typ}'"
        | .func _  => throwS s!"Cannot assign to function '{var}'"
        | .alias _ => throwS s!"Cannot assign to type alias '{var}'"

    | _         =>
      let (cl, l') ←
        handleLV <| Synth.LValue.small <| Synth.LValue.lvalue ctx lv
      let (cr, r') ←
        handle <| Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx e
      let ctx := {ctx with calls := cl.merge cr}
      if l'.typ.equiv r'.typ
      then
        match op with
        | .eq => return (ctx, .assign l' none r')
        | .aseq binop =>
          if l'.typ.equiv (.prim .int)
          then return (ctx, .assign l' (some <| Trans.int_binop binop) r')
          else throwS s!"Assignment with operations must have type '{Typ.prim .int}' not '{l'.typ}'"
      else throwS s!"Left side of assignment has type '{l'.typ}' doesn't match the right side '{r'.typ}'"

  | .ite cond tt ff =>
    let (calls, cond') ←
      handle <| Synth.Expr.small_nonvoid <|Synth.Expr.expr ctx cond
    let ctx' := {ctx with calls}
    match cond'.typ with
    | .prim .bool =>
      let (ctx1, tt') ← stmts ctx' tt
      let (ctx2, ff') ← stmts ctx' ff
      return (ctx1.join ctx2, .ite cond' tt' ff')
    | _ => throwS s!"If condition must be of type '{Typ.prim .bool}' not '{cond'.typ}'"

  | .while cond body =>
    let (calls, cond') ←
      handle <| Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx cond
    let ctx' := {ctx with calls}
    match cond'.typ with
    | .prim .bool =>
      let (ctx'', body') ← stmts ctx' body
      return ({ctx' with calls := ctx''.calls}, .while cond' body')
    | _ => throwS s!"Loop condition must be of type '{Typ.prim .bool}' not '{cond'.typ}'"

  | .return eOpt =>
    let calls_eOpt' ←
      eOpt.mapM (handle ∘ Synth.Expr.small_nonvoid ∘ Synth.Expr.expr ctx)
    let eOpt' := calls_eOpt'.map (fun (_, e') => e')
    let calls := calls_eOpt'.elim ctx.calls (fun (calls, _) => calls)
    let () ←
      match eOpt', ctx.ret_type with
      | none, none => pure ()
      | some e', some tau =>
        if e'.typ.equiv tau
        then pure ()
        else throw <| Error.stmt stm <|
          s!"Expected return type was '{ctx.ret_type}' but got '{e'.typ}'"
      | some e', _ =>
        throw <| Error.stmt stm <|
          s!"Expected return type was '{ctx.ret_type}' but got '{e'.typ}'"
      | none, _ =>
        throw <| Error.stmt stm <|
          s!"Expected return type is '{ctx.ret_type}'"

    let symbols' := ctx.symbols.mapVal (fun _ status =>
        match status with
        | .var vstatus => Status.Symbol.var {vstatus with initialised := true}
        | _ => status
      )
    let ctx' := {ctx with symbols := symbols', calls, returns := true}
    return (ctx', .«return» eOpt')

  | .assert e =>
    let (calls, e') ←
      handle <| Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx e
    match e'.typ with
    | .prim .bool => return ({ctx with calls}, .assert e')
    | _ => throwS s!"Assert condition must be of type '{Typ.prim .bool}' not '{e'.typ}'"

  | .exp e =>
    let (calls, e') ← handle <| Synth.Expr.small <| Synth.Expr.expr ctx e
    return ({ctx with calls}, .expr e')

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
  stmt ctx s => sizeOf s
  stmts ctx s => sizeOf s

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
    let fdecl := .fdecl ⟨ret, f.name, params⟩
    return (ctx', some fdecl)

def fdef (extern : Bool) (ctx : GlobalCtx) (f : Ast.FDef) : Result := do
  if extern
  then throw <| Error.func f.name <|
    s!"Function definintions cannot be in headers"
  else
    let (ctx', fctx, ret) ← func ctx extern true f.name f.type f.params
    let params : List (Typed Symbol) ← f.params.foldrM (fun p acc =>
        match Trans.type fctx p.type with
        | some ty => pure (⟨ty, p.name⟩ :: acc)
        | none => throw <| Error.func f.name <|
          s!"Function input must have non-void, declared type"
      ) []
    let (fctx', body') ←
      Stmt.stmts fctx f.body |>.tryCatch
        (fun err => throw {err with function := some f.name})
    let () ←
      if ret.isNone || fctx'.returns
      then pure ()
      else throw <| Error.func f.name <|
        s!"Function does not return on some paths"

    let funcCalls := ctx'.funcCalls.insert f.name fctx'.calls
    let calls := ctx'.calls.merge fctx'.calls

    let fdef := .fdef ⟨ret, f.name, params, body'⟩
    return ({ctx' with calls, funcCalls}, some fdef)

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

-- todo: add logic for headers also called functions
-- todo: preserve function call information (mostly for purity checks)
def typecheck (prog : Ast.Prog) : Except Error Tst.Prog := do
  let main_info := .func ⟨⟨some (.prim .int), []⟩, false⟩
  let main_sym := Symbol.main

  let init_symbols := Std.HashMap.empty.insert main_sym main_info
  let init_calls := Std.HashMap.empty.insert main_sym ()
  let init_context : GlobalCtx :=
    ⟨init_symbols, Std.HashMap.empty, init_calls, Std.HashMap.empty⟩

  let checkDec := fun extern (ctx, prog) g => do
    -- run through the program, carrying the global context
    let (ctx', gOpt) ← liftM <| Global.gdec extern ctx g
    match gOpt with
    | some g' => return (ctx', g' :: prog)
    | none => return (ctx', prog)

  prog.header.foldlM (m := Except Error) (checkDec true) (init_context, [])
  |>.bind (fun hres =>
    prog.program.foldlM (m := Except Error) (checkDec false) hres)
  |>.bind (fun ((ctx : GlobalCtx), (prog : List Tst.GDecl)) => do
    -- check the all called functions are defined
    let () ← Validate.callsDefined ctx main_sym
    -- program is reversed so flip it back
    return prog.reverse
  )
