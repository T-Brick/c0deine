import Std
import C0deine.Parser.Ast
import C0deine.Type.Typ
import C0deine.Type.Tst
import C0deine.Utils.Symbol
import C0deine.Utils.Comparison
import C0deine.Utils.Context

namespace C0deine.Typechecker

def Typed := Tst.Typed

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


def Trans.type [Ctx α] (ctx : α) : Ast.Typ → Option Typ
  | .int => some <| Typ.prim (Typ.Primitive.int)
  | .bool => some <| Typ.prim (Typ.Primitive.bool)
  | .tydef name =>
    match (Ctx.symbols ctx).find? name with
    | some (.alias tau) => some tau
    | _ => none
  | .ptr (tau : Ast.Typ) =>
    Trans.type ctx tau |>.map (Typ.mem ∘ Typ.Memory.pointer)
  | .arr (tau : Ast.Typ) =>
    Trans.type ctx tau |>.map (Typ.mem ∘ Typ.Memory.array)
  | .struct name => some <| Typ.mem (Typ.Memory.struct name)

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
                 : Except String (List Typ) :=
  params.foldrM (fun p acc =>
    match Trans.type ctx p.type with
    | some ty => pure (ty :: acc)
    | none => throw s!"Function input must have declared type"
  ) []


def Validate.global_var (ctx : GlobalCtx)
                        (var : Symbol)
                        (tau : Typ)
                        (initialised : Bool)
                        : Except String GlobalCtx := do
  if ¬Typ.isSmall tau
  then throw s!"Variable {var} must have a small type"
  else
    match ctx.symbols.find? var with
    | some (.var _) => throw s!"Variable {var} is declared twice"
    | some (.alias _) =>
      throw s!"Variable {var} is declared but also used as a type alias"
    | some (.func _) | none => -- allow shadowing of func declaration
      let symbols' := ctx.symbols.insert var (.var ⟨tau, initialised⟩)
      return  { ctx with symbols := symbols' }

def Validate.var (ctx : FuncCtx)
                 (var : Symbol)
                 (tau : Typ)
                 (initialised : Bool)
                 : Except String FuncCtx := do
  let ctx' := FuncCtx.toGlobalCtx ctx
  let gctx ← Validate.global_var ctx' var tau initialised
  return { ctx with symbols := gctx.symbols }

def Validate.typedef (ctx : GlobalCtx)
                     (var : Symbol)
                     (tau : Typ)
                     : Except String GlobalCtx := do
  if ctx.symbols.contains var
  then throw s!"Name for typedef {var} already used"
  else return {ctx with symbols := ctx.symbols.insert var (.alias tau)}

def Validate.fields (ctx : GlobalCtx)
                    (fields : List Ast.Field)
                    : Except String (List (Symbol × Typ)) :=
  fields.foldrM (fun field acc =>
    if acc.any (fun (f', _tau') => field.name == f')
    then throw s!"Struct field {field.name} appeared more than once"
    else
      match Trans.type ctx field.type with
      | some tau => pure ((field.name, tau) :: acc)
      | none => throw s!"Struct field must have a known type"
  ) []

def Validate.params (ctx : FuncCtx)
                    (params : List Ast.Param)
                    : Except String FuncCtx :=
  params.foldlM (fun ctx param =>
    match Trans.type ctx param.type with
    | none     => throw "Function paramter must have a known type"
    | some tau => Validate.var ctx param.name tau true
  ) ctx

-- does not add function to the global context!
def Validate.func (ctx : GlobalCtx)
                  (defining : Bool)
                  (name : Symbol)
                  (inputs : List Ast.Param)
                  (output : Option Typ)
                  : Except String (Status.Symbol × FuncCtx) := do
  let fctx := GlobalCtx.toFuncCtx name output ctx
  let intypes ← Trans.params fctx inputs
  let status := .func ⟨⟨output, intypes⟩, defining⟩
  let symbols' := fctx.symbols.insert name status
  let fctx ← Validate.params {fctx with symbols := symbols'} inputs
  if ¬(output.all Typ.isSmall)
  then throw s!"Function {name} must have small output type"
  else
    match ctx.symbols.find? name with
    | some (.var _var) =>
      throw s!"Function name {name} is already used as a variable"
    | some (.func f) =>
      if defining && f.defined
      then throw s!"Function {name} cannot be redefined"
      else if intypes ≠ f.type.args
      then throw s!"Function {name} inputs don't match prior declarations"
      else if output ≠ f.type.ret
      then throw s!"Function {name} return type differs from prior declarations"
      else return (status, fctx)
    | some (.alias _type) =>
      throw s!"Name {name} is already used as a type"
    | _ => return (status, fctx)

def Validate.callsDefined (ctx : GlobalCtx)
                          (main : Symbol)
                          : Except String Unit :=
  let err := fun name => throw s!"Function {name} is called but not defined"
  ctx.calls.foldM (fun () name () => do
    match ctx.symbols.find? name with
    | some (.func status) =>
      if status.defined
      then return ()
      else if name = main
      then throw s!"Function main must be defined"
      else err name
    | _ => err name
  ) ()


def Synth.intersect_types (tau1 tau2 : Typ.Check) : Except String Typ.Check := do
  match tau1, tau2 with
  | .any, _  => return tau2
  | _ , .any => return tau1
  | .type (.prim .int), .type (.prim .int)
  | .type (.prim .bool), .type (.prim .bool)
  | .void, .void   => return tau1
  | .type (.mem (.pointer tau1')), .type (.mem (.pointer tau2'))
  | .type (.mem (.array tau1')), .type (.mem (.array tau2'))     =>
    Synth.intersect_types (.type tau1') (.type tau2')
  | .type (.mem (.struct s1)), .type (.mem (.struct s2)) =>
    if s1 = s2
    then return tau1
    else throw "Cannot intersect incompatible types"
  | _, _ => throw "Cannot intersect incompatible types"


namespace Synth.Expr

def Result := Except String (Calls × Typed Tst.Expr)
deriving Inhabited

def binop_type (expect : Typ)
                     (lhs : Typ.Check)
                     (rhs : Typ.Check)
                     : Except String Typ := do
  let check := fun (ty : Typ) =>
    if expect = ty
    then pure ty
    else throw "Binary operator is not well-typed"
  match lhs, rhs with
  | .type (.prim .int), .type (.prim .int)
  | .type (.prim .int), .any
  | .any, .type (.prim .int)  => check (.prim .int)
  | .type (.prim .bool), .type (.prim .bool)
  | .type (.prim .bool), .any
  | .any, .type (.prim .bool) => check (.prim .bool)
  | .any, .any                => pure expect
  | _, _ => throw "Binary operator is not well-typed"

def nonvoid (res : Result) : Result := do
  let (calls, te) ← res
  match te.typ with
  | .void => throw "Expression cannot be void"
  | _ => return (calls, te)

def small (res : Result) : Result := do
  let (calls, te) ← res
  if te.typ.isSmall then return (calls, te)
  else throw "Expression has large type"

def small_nonvoid (res : Result) : Result := do
   let (calls, te) ← nonvoid res
   if te.typ.isSmall then return (calls, te)
   else throw "Expression has large type"

mutual
def expr (ctx : FuncCtx) (e : Ast.Expr) : Result := do
  match e with
  | .num n             =>
    let n : UInt32 ←
      if n = -2147483648 then
        pure 0x80000000
      else if h : 0 ≤ n ∧ n < UInt32.size then
        pure ⟨n.toNat, by cases n <;> simp at h
                          simp [Int.natAbs_ofNat]
                          exact h.2⟩
      else
        throw s!"Int literal {n} is not representable as a 32-bit signed integer"
    return (ctx.calls, ⟨.type (.prim (.int)), .num n⟩)
  | .«true»            =>
    return (ctx.calls, ⟨.type (.prim (.bool)), .«true»⟩)
  | .«false»           =>
    return (ctx.calls, ⟨.type (.prim (.bool)), .«false»⟩)
  | .null              =>
    return (ctx.calls, ⟨.any, .null⟩)
  | .unop op e         =>
    let (calls, te) ← small_nonvoid <| expr ctx e
    let (op', tau) ←
      match op, te.typ with
      | .int .neg, .type (.prim .int)
      | .int .neg, .any         => pure (.int .neg, .type (.prim .int))
      | .int .not, .type (.prim .int)
      | .int .not, .any         => pure (.int .not, .type (.prim .int))
      | .bool .neg, .type (.prim .bool)
      | .bool .neg, .any        => pure (.bool .neg, .type (.prim .bool))
      | _, _ => throw "Unary operator is not well-typed"
    return (calls, ⟨tau, .unop op' te⟩)

  | .binop op l r      =>
    let (cl, l') ← small_nonvoid <| expr ctx l
    let (cr, r') ← small_nonvoid <| expr ctx r
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
      | .int .rsh   => binop_type (.prim .int) l'.typ r'.typ
      | .bool .and
      | .bool .or
      | .cmp .less
      | .cmp .greater
      | .cmp .equal
      | .cmp .not_equal     => binop_type (.prim .bool) l'.typ r'.typ
      | .cmp .less_equal
      | .cmp .greater_equal =>
        if l'.typ = r'.typ
        then pure (.prim .bool)
        else throw "Binary operator is not well-typed"
    return (calls, ⟨.type tau, .binop (Trans.binop op) l' r'⟩)

  | .ternop cond tt ff =>
    let (cc, c') ← small_nonvoid <| expr ctx cond
    let (ct, tt') ← small_nonvoid <| expr ctx tt
    let (cf, ff') ← small_nonvoid <| expr ctx ff
    let calls := cc.merge ct |>.merge cf
    if c'.typ ≠ .type (.prim .bool)
    then throw "Ternary condition must be a bool"
    else
      let tau ← Synth.intersect_types tt'.typ ff'.typ
      return (calls, ⟨tau, .ternop c' tt' ff'⟩)

  | .app f args        =>
    match ctx.symbols.find? f with
    | some (.func status) =>
      let (calls, args') ← exprs ctx args
      let arg_types := args'.map (fun arg => arg.typ)
      let ret_type := -- return unit (i.e. void_star) if there's no return type
        match status.type.ret with
        | some tau => .type tau
        | none => .void
      if arg_types.length = status.type.args.length
      && (List.zip arg_types status.type.args
          |>.all fun (a, b) => Typ.Check.equiv a (.type b))
      then return (calls.insert f (), ⟨ret_type, .app f args'⟩)
      else throw "Function argument types don't match"
    | _ => throw "Cannot apply to a non-function type"

  | .alloc tau         =>
    let opt_tau' := Trans.type ctx tau
    match opt_tau' with
    | some tau' => return (ctx.calls, ⟨.type (.mem (.pointer tau')), .alloc tau'⟩)
    | none      => throw s!"Invalid allocation type"

  | .alloc_array tau e =>
    let opt_tau' := Trans.type ctx tau
    let (calls, e') ← small_nonvoid <| expr ctx e
    match opt_tau', e'.typ with
    | none, _ => throw s!"Invalid array type"
    | some tau', .type (.prim .int) =>
      return (calls, ⟨.type (.mem (.array tau')), .alloc_array tau' e'⟩)
    | _, _ => throw "Array length must be an integer"

  | .var name          =>
    match ctx.symbols.find? name with
    | some (.var status) =>
      if status.initialised
      then return (ctx.calls, ⟨.type status.type, .var name⟩)
      else throw s!"Variable {name} not initialised"
    | _ => throw s!"Variable {name} not declared"

  | .dot e field       =>
    let (calls, e') ← expr ctx e
    match e'.typ with
    | .type (.mem (.pointer <| .mem (.struct name))) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw s!"Struct {name} is not defined"
        else
          match status.fields.find? field with
          | some tau => return (calls, ⟨.type tau, .dot e' field⟩)
          | none => throw s!"Invalid field {field}}"
      | none => throw s!"Struct {name} is not defined"
    | _ => throw s!"Arrow operator must be used on a struct pointer"

  | .arrow e field     =>
    let (calls, e') ← nonvoid <| expr ctx e
    match e'.typ with
    | .type (.mem (.struct name)) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw s!"Struct {name} is not defined"
        else
          match status.fields.find? field with
          | some tau => return (calls, ⟨.type tau, .dot e' field⟩)
          | none => throw s!"Invalid field {field}}"
      | none => throw s!"Struct {name} is not defined"
    | _ => throw s!"Field accessor can only operate on a struct"

  | .deref e           =>
    let (calls, e') ← small <| expr ctx e
    match e'.typ with
    | .any => throw "Cannot dereference a null pointer/function"
    | .type (.mem (.pointer tau))  => return (calls, ⟨.type tau, .deref e'⟩)
    | _ => throw "Cannot dereference a non-pointer type"

  | .index arr indx    =>
    let (ca, arr') ← small_nonvoid <| expr ctx arr
    let (ci, index') ← small_nonvoid <| expr ctx indx
    let calls := ca.merge ci
    match arr'.typ, index'.typ with
    | .type (.mem (.array tau)), .type (.prim .int) =>
      return (calls, ⟨.type tau, .index arr' index'⟩)
    | .type (.mem (.array _tau)), _ => throw "Array indices must be integers"
    | _, _ => throw "Indexing can only be done on array types"

def exprs (ctx : FuncCtx)
          (exps : List Ast.Expr)
          : Except String (Calls × List (Typed Tst.Expr)) := do
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

def Result := Except String (Calls × Typed Tst.LValue)
deriving Inhabited

def small (res : Result) : Result := do
  let (calls, tv) ← res
  if tv.typ.isSmall
  then return (calls, tv)
  else throw "LValue has large type"

mutual
def lvalue (ctx : FuncCtx) (lv : Ast.LValue) : Result := do
  match lv with
  | .var name => var ctx name
  | .dot lv field => dot ctx lv field
  | .arrow lv field => arrow ctx lv field
  | .deref lv => deref ctx lv
  | .index lv indx => index ctx lv indx

def var (ctx : FuncCtx) (var : Symbol) : Result := do
  match ctx.symbols.find? var with
  | some (.var status) =>
    if status.initialised
    then return (ctx.calls, ⟨.type status.type, .var var⟩)
    else throw s!"Variable {var} not initialised"
  | _ => throw s!"Variable {var} not declared"

def dot (ctx : FuncCtx) (lv : Ast.LValue) (field : Symbol) : Result := do
  let (calls, lv') ← lvalue ctx lv
  match lv'.typ with
  | .type (.mem (.pointer <| .mem (.struct name))) =>
    match ctx.structs.find? name with
    | some status =>
      if ¬status.defined
      then throw s!"Struct {name} is not defined"
      else
        match status.fields.find? field with
        | some tau => return (calls, ⟨.type tau, .dot lv' field⟩)
        | none => throw s!"Invalid field {field}}"
    | none => throw s!"Struct {name} is not defined"
  | _ => throw s!"Arrow operator must be used on a struct pointer"

def arrow (ctx : FuncCtx)
                (e : Ast.LValue)
                (field : Ast.Ident)
                : Result := do
  let (calls, e') ← lvalue ctx e
  match e'.typ with
  | .type (.mem (.struct name)) =>
    match ctx.structs.find? name with
    | some status =>
      if ¬status.defined
      then throw s!"Struct {name} is not defined"
      else
        match status.fields.find? field with
        | some tau => return (calls, ⟨.type tau, .dot e' field⟩)
        | none => throw s!"Invalid field {field}}"
    | none => throw s!"Struct {name} is not defined"
  | _ => throw s!"Field accessor can only operate on a struct"

def deref (ctx : FuncCtx) (e : Ast.LValue) : Result := do
  let (calls, e') ← lvalue ctx e
  match e'.typ with
  | .type (.mem (.pointer tau))  => return (calls, ⟨.type tau, .deref e'⟩)
  | _ => throw "Cannot dereference a non-pointer type"

def index (ctx : FuncCtx)
                (arr : Ast.LValue)
                (index : Ast.Expr)
                : Result := do
  let (ca, arr') ← lvalue ctx arr
  let (ci, index') ← Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx index
  let calls := ca.merge ci
  match arr'.typ, index'.typ with
  | .type (.mem (.array tau)), .type (.prim .int) =>
    return (calls, ⟨.type tau, .index arr' index'⟩)
  | .type (.mem (.array _tau)), _ => throw "Array indices must be integers"
  | _, _ => throw "Indexing can only be done on array types"
end

end Synth.LValue


namespace Stmt

def Result := Except String (FuncCtx × Tst.Stmt)
deriving Inhabited

mutual
def stmt (ctx : FuncCtx) (s : Ast.Stmt) : Result := do
  match s with
  | .decl type name init body =>
    let opt_tau := Trans.type ctx type
    match opt_tau with
    | none => throw s!"Variable {name} must have declared type"
    | some tau =>
      let ctx' ← Validate.var ctx name tau (init.isSome)
      let (calls, init') ←
        match init with
        | none => pure (ctx.calls, none)
        | some e =>
          let (calls, e') ← Synth.Expr.expr ctx e
          if e'.typ = .type tau
          then pure (calls, some e')
          else throw s!"Variable {name} has mismatched types"
      -- don't use new context since no longer in scope, but keep calls, returns
      let (ctx'', body') ← stmts {ctx' with calls} body
      let calledOldCtx :=
        { ctx with calls := ctx''.calls, returns := ctx''.returns }
      return (calledOldCtx, .decl ⟨.type tau, name⟩ init' body'.reverse)

  | .assn lv op e =>
    match lv with
    | .var var =>
      let elab_e :=
        match op with
        | .eq => e
        | .aseq binop => .binop (.int binop) (.var var) e
      match ctx.symbols.find? var with
      | none => throw s!"Variable {var} must be initialised before assignment"
      | some status =>
        match status with
        | .var vstatus =>
          let (calls, e') ← Synth.Expr.small <| Synth.Expr.expr ctx elab_e
          let ctx := {ctx with calls}
          if e'.typ.equiv <| .type vstatus.type
          then
            let ctx' :=
              match vstatus.initialised with
              | true  => ctx
              | false =>
                { ctx with
                    symbols := ctx.symbols.insert var (.var ⟨vstatus.type, true⟩)
                }
            return (ctx', .assign ⟨e'.typ, .var var⟩ none e')
          else throw s!"Assignment of {var} has mismatched types"
        | .func _  => throw s!"Cannot assign to function {var}"
        | .alias _ => throw s!"Cannot assign to type alias {var}"

    | _         =>
      let (cl, l') ← Synth.LValue.small <| Synth.LValue.lvalue ctx lv
      let (cr, r') ← Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx e
      let ctx := {ctx with calls := cl.merge cr}
      if l'.typ.equiv r'.typ
      then
        match op with
        | .eq => return (ctx, .assign l' none r')
        | .aseq binop =>
          if l'.typ.equiv (.type <| .prim .int)
          then return (ctx, .assign l' (some <| Trans.int_binop binop) r')
          else throw "Assignment with operations must have integer types"
      else throw "Assignment types mismatch"

  | .ite cond tt ff =>
    let (calls, cond') ← Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx cond
    let ctx := {ctx with calls}
    match cond'.typ with
    | .type (.prim .bool) =>
      let (ctx1, tt') ← stmts ctx tt
      let (ctx2, ff') ← stmts ctx ff
      return (ctx1.join ctx2, .ite cond' tt' ff')
    | _ => throw "If condition must be of type bool"

  | .while cond body =>
    let (calls, cond') ← Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx cond
    let ctx := {ctx with calls}
    match cond'.typ with
    | .type (.prim .bool) =>
      let (ctx'', body') ← stmts ctx body
      return ({ctx'' with calls := ctx''.calls}, .while cond' body')
    | _ => throw "Loop guard must be of type bool"

  | .return eOpt =>
    let calls_eOpt' ← eOpt.mapM (Synth.Expr.small_nonvoid ∘ Synth.Expr.expr ctx)
    let eOpt' := calls_eOpt'.map (fun (_, e') => e')
    let calls := calls_eOpt'.elim ctx.calls (fun (calls, _) => calls)
    let ret_type ← eOpt'.mapM (fun e' =>
        match e'.typ with
        | .type t => pure t
        | _ => throw "Return type is not a valid type"
      )
    if ret_type = ctx.ret_type
    then
      let symbols' := ctx.symbols.mapVal (fun _ status =>
          match status with
          | .var vstatus => Status.Symbol.var {vstatus with initialised := true}
          | _ => status
        )
      let ctx' := {ctx with symbols := symbols', calls, returns := true}
      return (ctx', .«return» eOpt')
    else throw "Return types mismatch"

  | .assert e =>
    let (calls, e') ← Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx e
    match e'.typ with
    | .type (.prim .bool) => return ({ctx with calls}, .assert e')
    | _ => throw "Assert condition must be of type bool"

  | .exp e =>
    let (calls, e') ← Synth.Expr.small <| Synth.Expr.expr ctx e
    return ({ctx with calls}, .expr e')

def stmts (ctx : FuncCtx)
          (body : List Ast.Stmt)
          : Except String (FuncCtx × List Tst.Stmt) := do
  match body with
  | [] => return (ctx, [])
  | b::bs =>
    let (ctx', b') ← stmt ctx b
    let (ctx'', bs') ← stmts ctx' bs
    return (ctx'', bs'.append [b'])
end

termination_by
  stmt ctx s => sizeOf s
  stmts ctx s => sizeOf s

end Stmt

namespace Global

def Result := Except String (GlobalCtx × Option Tst.GDecl)
deriving Inhabited

def func (ctx : GlobalCtx)
         (defining : Bool)
         (name : Ast.Ident)
         (ret : Option Ast.Typ)
         (params : List Ast.Param)
         : Except String (GlobalCtx × FuncCtx × Option Typ) := do
  let ret' ← ret.mapM (fun ret =>
      match Trans.type ctx ret with
      | some ret' => pure ret'
      | none => throw s!"Function {name} must have a declared type"
    )

  let (status, fctx) ← Validate.func ctx defining name params ret'
  let status' ←
    match ctx.symbols.find? name with
    | some (.func f) =>
      if defining && f.defined
      then throw s!"Function {name} was already defined"
      else pure (.func {f with defined := f.defined || defining})
    | some _ => throw s!"Function {name} collides with another name"
    | none => pure status

  let symbols := ctx.symbols.insert name status'
  let funcCalls := ctx.funcCalls.insert name fctx.calls
  let calls := ctx.calls.merge fctx.calls

  return ({ctx with symbols, funcCalls, calls}, fctx, ret')

def fdecl (extern : Bool) (ctx : GlobalCtx) (f : Ast.FDecl) : Result := do
  if extern && "main" == f.name.name
  then throw s!"Function main cannot appear in headers"
  else
    let (ctx', fctx, ret) ← func ctx false f.name f.type f.params
    let params ← Trans.params fctx f.params
    let fdecl := .fdecl ⟨ret, f.name, params⟩
    return (ctx', some fdecl)

def fdef (extern : Bool) (ctx : GlobalCtx) (f : Ast.FDef) : Result := do
  if extern
  then throw s!"Function definintions cannot be in headers"
  else
    let (ctx', fctx, ret) ← func ctx true f.name f.type f.params
    let params : List (Typed Symbol) ← f.params.foldrM (fun p acc =>
        match Trans.type fctx p.type with
        | some ty => pure (⟨.type ty, p.name⟩ :: acc)
        | none => throw s!"Function input must have non-void, declared type"
      ) []
    let (fctx', body') ← Stmt.stmts fctx f.body
    let () ←
      if ret.isNone || fctx'.returns
      then pure ()
      else throw s!"Function {fctx'.name} does not return on some paths"
    let fdef := .fdef ⟨ret, f.name, params, body'⟩
    return (ctx', some fdef)

def tydef (ctx : GlobalCtx) (t : Ast.TyDef) : Result := do
  let tau' ←
    match Trans.type ctx t.type with
    | some tau => pure tau
    | none => throw s!"Typedef must have a non-void, known type"
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
      then throw s!"Struct {s.name} has already been declared"
      else pure ()
    | none => pure ()
  let fieldsMap ← Validate.fields ctx s.fields
  let status := ⟨Std.HashMap.ofList fieldsMap, true⟩
  let structs' := ctx.structs.insert s.name status
  let fields' := fieldsMap.map (fun (field, tau) => ⟨.type tau, field⟩)
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
def typecheck (ast : Ast.Prog) : ExceptT String Context Tst.Prog := do
  let main_info := .func ⟨⟨some (.prim .int), []⟩, false⟩
  let main_sym ← Symbol.symbol "main"

  let init_symbols := Std.HashMap.empty.insert main_sym main_info
  let init_calls := Std.HashMap.empty.insert main_sym ()
  let init_context : GlobalCtx :=
    ⟨init_symbols, Std.HashMap.empty, init_calls, Std.HashMap.empty⟩

  ast.foldlM (m := ExceptT _ Context) (fun (ctx, prog) g => do
    -- run through the program, carrying the global context
    let (ctx', gOpt) ← liftM <| Global.gdec false ctx g
    match gOpt with
    | some g' => return (ctx', g' :: prog)
    | none => return (ctx', prog)
  ) (init_context, [])
  |>.bind (fun ((ctx : GlobalCtx), (prog : List Tst.GDecl)) => do
    -- check the all called functions are defined
    let () ← Validate.callsDefined ctx main_sym
    -- program is reversed so flip it back
    return prog.reverse
  )
