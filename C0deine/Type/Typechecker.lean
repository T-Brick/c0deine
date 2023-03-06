import Std
import C0deine.Parser.Ast
import C0deine.Type.Typ
import C0deine.Type.Tst
import C0deine.Utils.Symbol
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

structure FuncCtx where
  symbols : SymbolTable
  structs : StructTable
  ret_type : Option Typ
  returns : Bool

structure GlobalCtx where
  symbols : SymbolTable
  structs : StructTable

-- joins two contexts together, assuming non-variables are the same
def FuncCtx.join (ctx1 ctx2 : FuncCtx) : FuncCtx :=
  let returns := ctx1.returns && ctx2.returns
  let intersect :=
    fun var status =>
      match status, ctx2.symbols.find? var with
      | .var v1, some (.var v2) =>
        some (.var ⟨v1.type, v1.initialised && v2.initialised⟩)
      | _, none => none
      | _, _    => some status
  let symbols := ctx1.symbols.filterMap intersect
  ⟨symbols, ctx1.structs, ctx1.ret_type, returns⟩


def Trans.type (ctx : FuncCtx) : Ast.Typ → Option Typ
  | .int => some <| Typ.prim (Typ.Primitive.int)
  | .bool => some <| Typ.prim (Typ.Primitive.bool)
  | .void => none
  | .tydef name =>
    match ctx.symbols.find? name with
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

-- todo: we should prove that these actually do what we want
def Validate.var (ctx : FuncCtx)
                 (var : Symbol)
                 (tau : Typ)
                 (initialised : Bool)
                 : Except String FuncCtx := do
  if ¬Typ.isSmall tau
  then throw s!"Variable {var} must have a small type"
  else
    match ctx.symbols.find? var with
    | some (.var _) => throw s!"Variable {var} is declared twice"
    | some (.alias _) =>
      throw s!"Variable {var} is declared but also used as a type alias"
    | some (.func _) | none => -- allow shadowing of func declaration
      return {ctx with symbols := ctx.symbols.insert var (.var ⟨tau, initialised⟩)}

def Validate.typedef (ctx : FuncCtx)
                     (var : Symbol)
                     (tau : Typ)
                     : Except String FuncCtx := do
  if ctx.symbols.contains var
  then throw s!"Name for typedef {var} already used"
  else return {ctx with symbols := ctx.symbols.insert var (.alias tau)}

def Validate.params (ctx : FuncCtx)
                    (params : List Ast.Param)
                    : Except String FuncCtx := do
  match params with
  | .nil => return ctx
  | .cons p ps =>
    match Trans.type ctx p.type with
    | none     => throw "Function paramter has void or unknown type"
    | some tau =>
      let ctx' ← Validate.var ctx p.name tau true
      Validate.params ctx' ps

-- does not add function to the context!
def Validate.func (ctx : FuncCtx)
                  (name : Symbol)
                  (inputs : List Ast.Param)
                  (output : Option Typ)
                  : Except String FuncCtx := do
  if ctx.symbols.contains name
  then throw s!"Name for function {name} already used"
  else if ¬(output.all Typ.isSmall)
  then throw s!"Function {name} must have small output type"
  else Validate.params ctx inputs

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

def Result := Except String (Tst.Typed Tst.Expr)
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
  let v ← res
  match v.typ with
  | .void => throw "Expression cannot be void"
  | _ => return v

def small (res : Result) : Result := do
  let v ← res
  if v.typ.isSmall then return v
  else throw "Expression has large type"

def small_nonvoid (res : Result) : Result := do
   let v ← nonvoid res
   if v.typ.isSmall then return v
   else throw "Expression has large type"

mutual
partial def expr (ctx : FuncCtx) (e : Ast.Expr) : Result := do
  match e with
  | .num n             => return ⟨.type (.prim (.int)), .num n⟩
  | .«true»            => return ⟨.type (.prim (.bool)), .«true»⟩
  | .«false»           => return ⟨.type (.prim (.bool)), .«false»⟩
  | .null              => return ⟨.any, .null⟩
  | .unop op e         => unop ctx op e
  | .binop op l r      => binop ctx op l r
  | .ternop cond tt ff => ternop ctx cond tt ff
  | .app f args        => app ctx f args
  | .alloc ty          => alloc ctx ty
  | .alloc_array ty e  => alloc_array ctx ty e
  | .var name          => var ctx name
  | .dot e field       => dot ctx e field
  | .arrow e field     => arrow ctx e field
  | .deref e           => deref ctx e
  | .index e indx      => index ctx e indx

partial def unop (ctx : FuncCtx)
               (op : Ast.UnOp)
               (e : Ast.Expr)
               : Result := do
  let te ← small_nonvoid <| expr ctx e
  let (op', tau) ←
    match op, te.typ with
    | .int .neg, .type (.prim .int)
    | .int .neg, .any         => pure (.int .neg, .type (.prim .int))
    | .int .not, .type (.prim .int)
    | .int .not, .any         => pure (.int .not, .type (.prim .int))
    | .bool .neg, .type (.prim .bool)
    | .bool .neg, .any        => pure (.bool .neg, .type (.prim .bool))
    | _, _ => throw "Unary operator is not well-typed"
  return ⟨tau, .unop op' te⟩

partial def binop (ctx : FuncCtx)
                (op : Ast.BinOp)
                (l r : Ast.Expr)
                : Result := do
  let l' ← small_nonvoid <| expr ctx l
  let r' ← small_nonvoid <| expr ctx r
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
  return ⟨.type tau, .binop (Trans.binop op) l' r'⟩

partial def ternop (ctx : FuncCtx) (c tt ff : Ast.Expr) : Result := do
  let c' ← small_nonvoid <| expr ctx c
  let tt' ← small_nonvoid <| expr ctx tt
  let ff' ← small_nonvoid <| expr ctx ff
  if c'.typ ≠ .type (.prim .bool)
  then throw "Ternary condition must be a bool"
  else
    let tau ← Synth.intersect_types tt'.typ ff'.typ
    return ⟨tau, .ternop c' tt' ff'⟩

partial def app (ctx : FuncCtx)
              (f : Ast.Ident)
              (args : List Ast.Expr)
              : Result := do
  match ctx.symbols.find? f with
  | some (.func status) =>
    let args' ← args.mapM (small_nonvoid ∘ expr ctx)
    let arg_types := args'.map (fun arg => arg.typ)
    let ret_type := -- return unit (i.e. void_star) if there's no return type
      match status.type.ret with
      | some tau => .type tau
      | none => .void
    if arg_types.length = status.type.args.length
    && (List.zip arg_types status.type.args
        |>.all fun (a, b) => Typ.Check.equiv a (.type b))
    then return ⟨ret_type, .app f args'⟩
    else throw "Function argument types don't match"
  | _ => throw "Cannot apply to a non-function type"

partial def alloc (ctx : FuncCtx) (tau : Ast.Typ) : Result := do
  let opt_tau' := Trans.type ctx tau
  match opt_tau' with
  | some tau' => return ⟨.type (.mem (.pointer tau')), .alloc tau'⟩
  | none      => throw s!"Invalid allocation type"

partial def alloc_array (ctx : FuncCtx)
                      (tau : Ast.Typ)
                      (e : Ast.Expr)
                      : Result := do
  let opt_tau' := Trans.type ctx tau
  let e' ← small_nonvoid <| expr ctx e
  match opt_tau', e'.typ with
  | none, _ => throw s!"Invalid array type"
  | some tau', .type (.prim .int) =>
    return ⟨.type (.mem (.array tau')), .alloc_array tau' e'⟩
  | _, _ => throw "Array length must be an integer"

partial def var (ctx : FuncCtx) (var : Ast.Ident) : Result := do
  match ctx.symbols.find? var with
  | some (.var status) =>
    if status.initialised
    then return ⟨.type status.type, .var var⟩
    else throw s!"Variable {var} not initialised"
  | _ => throw s!"Variable {var} not declared"

partial def dot (ctx : FuncCtx)
              (e : Ast.Expr)
              (field : Ast.Ident)
              : Result := do
  let e' ← expr ctx e
  match e'.typ with
  | .type (.mem (.pointer <| .mem (.struct name))) =>
    match ctx.structs.find? name with
    | some status =>
      if ¬status.defined
      then throw s!"Struct {name} is not defined"
      else
        match status.fields.find? field with
        | some tau => return ⟨.type tau, .dot e' field⟩
        | none => throw s!"Invalid field {field}}"
    | none => throw s!"Struct {name} is not defined"
  | _ => throw s!"Arrow operator must be used on a struct pointer"

partial def arrow (ctx : FuncCtx)
                (e : Ast.Expr)
                (field : Ast.Ident)
                : Result := do
  let e' ← nonvoid <| expr ctx e
  match e'.typ with
  | .type (.mem (.struct name)) =>
    match ctx.structs.find? name with
    | some status =>
      if ¬status.defined
      then throw s!"Struct {name} is not defined"
      else
        match status.fields.find? field with
        | some tau => return ⟨.type tau, .dot e' field⟩
        | none => throw s!"Invalid field {field}}"
    | none => throw s!"Struct {name} is not defined"
  | _ => throw s!"Field accessor can only operate on a struct"

partial def deref (ctx : FuncCtx) (e : Ast.Expr) : Result := do
  let e' ← small <| expr ctx e
  match e'.typ with
  | .any => throw "Cannot dereference a null pointer/function"
  | .type (.mem (.pointer tau))  => return ⟨.type tau, .deref e'⟩
  | _ => throw "Cannot dereference a non-pointer type"

partial def index (ctx : FuncCtx)
                (arr : Ast.Expr)
                (index : Ast.Expr)
                : Result := do
  let arr' ← small_nonvoid <| expr ctx arr
  let index' ← small_nonvoid <| expr ctx index
  match arr'.typ, index'.typ with
  | .type (.mem (.array tau)), .type (.prim .int) =>
    return ⟨.type tau, .index arr' index'⟩
  | .type (.mem (.array _tau)), _ => throw "Array indices must be integers"
  | _, _ => throw "Indexing can only be done on array types"
end

-- termination_by
  -- expr ctx e => sizeOf e
  -- unop ctx op e => sizeOf e
  -- binop ctx op l r => sizeOf l + sizeOf r
  -- ternop ctx cc tt ff => sizeOf cc + sizeOf tt + sizeOf ff
  -- app ctx f args => sizeOf args
  -- alloc_array ctx tau e => sizeOf e
  -- dot ctx e f => sizeOf e
  -- arrow ctx e f => sizeOf e
  -- deref ctx e => sizeOf e
  -- index ctx arr ind => sizeOf arr + sizeOf ind

end Synth.Expr

namespace Synth.LValue

def Result := Except String (Tst.Typed Tst.LValue)
deriving Inhabited

def small (res : Result) : Result := do
  let v ← res
  if v.typ.isSmall
  then return v
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
    then return ⟨.type status.type, .var var⟩
    else throw s!"Variable {var} not initialised"
  | _ => throw s!"Variable {var} not declared"

def dot (ctx : FuncCtx) (lv : Ast.LValue) (field : Symbol) : Result := do
  let lv' ← lvalue ctx lv
  match lv'.typ with
  | .type (.mem (.pointer <| .mem (.struct name))) =>
    match ctx.structs.find? name with
    | some status =>
      if ¬status.defined
      then throw s!"Struct {name} is not defined"
      else
        match status.fields.find? field with
        | some tau => return ⟨.type tau, .dot lv' field⟩
        | none => throw s!"Invalid field {field}}"
    | none => throw s!"Struct {name} is not defined"
  | _ => throw s!"Arrow operator must be used on a struct pointer"

def arrow (ctx : FuncCtx)
                (e : Ast.LValue)
                (field : Ast.Ident)
                : Result := do
  let e' ← lvalue ctx e
  match e'.typ with
  | .type (.mem (.struct name)) =>
    match ctx.structs.find? name with
    | some status =>
      if ¬status.defined
      then throw s!"Struct {name} is not defined"
      else
        match status.fields.find? field with
        | some tau => return ⟨.type tau, .dot e' field⟩
        | none => throw s!"Invalid field {field}}"
    | none => throw s!"Struct {name} is not defined"
  | _ => throw s!"Field accessor can only operate on a struct"

def deref (ctx : FuncCtx) (e : Ast.LValue) : Result := do
  let e' ← lvalue ctx e
  match e'.typ with
  | .type (.mem (.pointer tau))  => return ⟨.type tau, .deref e'⟩
  | _ => throw "Cannot dereference a non-pointer type"

def index (ctx : FuncCtx)
                (arr : Ast.LValue)
                (index : Ast.Expr)
                : Result := do
  let arr' ← lvalue ctx arr
  let index' ← Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx index
  match arr'.typ, index'.typ with
  | .type (.mem (.array tau)), .type (.prim .int) =>
    return ⟨.type tau, .index arr' index'⟩
  | .type (.mem (.array _tau)), _ => throw "Array indices must be integers"
  | _, _ => throw "Indexing can only be done on array types"
end

end Synth.LValue


namespace Stmt

def Result := Except String (FuncCtx × Tst.Stmt)
deriving Inhabited

mutual
partial def stmt (ctx : FuncCtx) (s : Ast.Stmt) : Result :=
  match s with
  | .decl type name init body => decl ctx type name init body
  | .assn lv op e =>
    match lv with
    | .var name => assn_var ctx name op e
    | _         => assn_dest ctx lv op e
  | .ite cond tt ff => ite ctx cond tt ff
  | .while cond body => «while» ctx cond body
  | .return eOpt => «return» ctx eOpt
  | .assert e => assert ctx e
  | .exp e => exp ctx e

partial def stmts (ctx : FuncCtx)
          (body : List Ast.Stmt)
          : Except String (FuncCtx × List Tst.Stmt) := do
  let (ctx', body') ← body.foldlM (
    fun (ctx', body') s => do
      let (ctx', s') ← stmt ctx' s
      pure (ctx', s' :: body')
    ) (ctx, [])
  return (ctx', body'.reverse)

partial def decl (ctx : FuncCtx)
         (type : Ast.Typ)
         (name : Ast.Ident)
         (init : Option Ast.Expr)
         (body : List Ast.Stmt)
         : Result := do
  let opt_tau := Trans.type ctx type
  match opt_tau with
  | none => throw s!"Variable {name} must have non-void, declared type"
  | some tau =>
    let ctx' ← Validate.var ctx name tau (init.isSome)
    let init' ← do
      match init with
      | none => pure none
      | some e =>
        let e' ← Synth.Expr.expr ctx e
        if e'.typ = .type tau
        then pure (some e')
        else throw s!"Variable {name} has mismatched types"
    -- don't use new context since no longer in scope
    let (_, body') ← stmts ctx' body
    return (ctx, .decl ⟨.type tau, name⟩ init' body'.reverse)

partial def assn_var (ctx : FuncCtx)
             (var : Ast.Ident)
             (op : Ast.AsnOp)
             (e : Ast.Expr)
             : Result := do
  let elab_e :=
    match op with
    | .eq => e
    | .aseq binop => .binop (.int binop) (.var var) e
  match ctx.symbols.find? var with
  | none => throw s!"Variable {var} must be initialised before assignment"
  | some status =>
    match status with
    | .var vstatus =>
      let e' ← Synth.Expr.small <| Synth.Expr.expr ctx elab_e
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

partial def assn_dest (ctx : FuncCtx)
              (l : Ast.LValue)
              (op : Ast.AsnOp)
              (r : Ast.Expr)
              : Result := do
  let l' ← Synth.LValue.small <| Synth.LValue.lvalue ctx l
  let r' ← Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx r
  if l'.typ.equiv r'.typ
  then
    match op with
    | .eq => return (ctx, .assign l' none r')
    | .aseq binop =>
      if l'.typ.equiv (.type <| .prim .int)
      then return (ctx, .assign l' (some <| Trans.int_binop binop) r')
      else throw "Assignment with operations must have integer types"
  else throw "Assignment types mismatch"

partial def ite (ctx : FuncCtx)
        (cond : Ast.Expr)
        (tt : Ast.Stmt)
        (ff : Ast.Stmt)
        : Result := do
  let cond' ← Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx cond
  match cond'.typ with
  | .type (.prim .bool) =>
    let (ctx1, tt') ← stmt ctx tt
    let (ctx2, ff') ← stmt ctx ff
    return (ctx1.join ctx2, .ite cond' tt' ff')
  | _ => throw "If condition must be of type bool"

partial def «while» (ctx : FuncCtx)
            (cond : Ast.Expr)
            (body : List Ast.Stmt)
            : Result := do
  let cond' ← Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx cond
  match cond'.typ with
  | .type (.prim .bool) =>
    let (_, body') ← stmts ctx body
    return (ctx, .while cond' body')
  | _ => throw "Loop guard must be of type bool"

partial def «return» (ctx : FuncCtx) (eOpt : Option Ast.Expr) : Result := do
  let eOpt' ← eOpt.mapM (Synth.Expr.small_nonvoid ∘ Synth.Expr.expr ctx)
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
    let ctx' := {ctx with symbols := symbols', returns := true}
    return (ctx', .«return» eOpt')
  else throw "Return types mismatch"

partial def assert (ctx : FuncCtx) (e : Ast.Expr) : Result := do
  let e' ← Synth.Expr.small_nonvoid <| Synth.Expr.expr ctx e
  match e'.typ with
  | .type (.prim .bool) => return (ctx, .assert e')
  | _ => throw "Assert condition must be of type bool"

partial def exp (ctx : FuncCtx) (e : Ast.Expr) : Result := do
  let e' ← Synth.Expr.small <| Synth.Expr.expr ctx e
  return (ctx, .expr e')

end

end Stmt

