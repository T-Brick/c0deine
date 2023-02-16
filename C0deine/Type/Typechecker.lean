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


def Trans.type (ctx : FuncCtx) : Ast.Typ → Option Typ
  | .int => some <| Typ.prim (Typ.Primitive.int)
  | .bool => some <| Typ.prim (Typ.Primitive.bool)
  | .void => none
  | .tydef name =>
    match ctx.symbols.find? name with
    | some (.alias tau) => some tau
    | _ => none
  | .ptr (.void) => some Typ.void_star
  | .ptr (tau : Ast.Typ) =>
    Trans.type ctx tau |>.map (Typ.mem ∘ Typ.Memory.pointer)
  | .arr (tau : Ast.Typ) =>
    Trans.type ctx tau |>.map (Typ.mem ∘ Typ.Memory.array)
  | .struct name => some <| Typ.mem (Typ.Memory.struct name)

def Trans.binop : Ast.BinOp → Tst.BinOp
  | .int .plus  => .int .plus
  | .int .minus => .int .minus
  | .int .times => .int .times
  | .int .div   => .int .div
  | .int .mod   => .int .mod
  | .int .and   => .int .and
  | .int .xor   => .int .xor
  | .int .or    => .int .or
  | .int .lsh   => .int .lsh
  | .int .rsh   => .int .rsh
  | .cmp .lt    => .cmp .less
  | .cmp .le    => .cmp .greater
  | .cmp .gt    => .cmp .equal
  | .cmp .ge    => .cmp .not_equal
  | .cmp .eq    => .cmp .less_equal
  | .cmp .ne    => .cmp .greater_equal
  | .bool .and  => .bool .and
  | .bool .or   => .bool .or



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

def Synth.ExprResult := Except String (Tst.Typed Tst.Expr)

def Synth.binop_type (expect : Typ)
                     (lhs : Typ)
                     (rhs : Typ)
                     : Except String Typ := do
  let check := fun ty =>
    if expect = ty
    then pure ty
    else throw "Binary operator is not well-typed"
  match lhs, rhs with
  | .prim .int, .prim .int
  | .prim .int, .any
  | .any, .prim .int          => check (.prim .int)
  | .prim .bool, .prim .bool
  | .prim .bool, .any
  | .any, .prim .bool         => check (.prim .bool)
  | .any, .any                => pure expect
  | _, _ => throw "Binary operator is not well-typed"

def Synth.intersect_types (tau1 tau2 : Typ) : Except String Typ := do
  match tau1, tau2 with
  | .any, _  => return tau2
  | _ , .any => return tau1
  | .prim .int, .prim .int
  | .prim .bool, .prim .bool
  | .void_star, .void_star   => return tau1
  | .mem (.pointer tau1'), .mem (.pointer tau2')
  | .mem (.array tau1'), .mem (.array tau2')     =>
    Synth.intersect_types tau1' tau2'
  | .mem (.struct s1), .mem (.struct s2) =>
    if s1 = s2
    then return tau1
    else throw "Cannot intersect incompatible types"
  | _, _ => throw "Cannot intersect incompatible types"

mutual
def Synth.expr (ctx : FuncCtx) (e : Ast.Expr) : Synth.ExprResult := do
  match e with
  | .num n             => return ⟨.prim (.int), .num n⟩
  | .«true»            => return ⟨.prim (.bool), .«true»⟩
  | .«false»           => return ⟨.prim (.bool), .«false»⟩
  | .null              => return ⟨.mem (.pointer .any), .null⟩
  | .unop op e         => Synth.unop ctx op e
  | .binop op l r      => Synth.binop ctx op l r
  | .ternop cond tt ff => Synth.ternop ctx cond tt ff
  | .app f args        => Synth.app ctx f args
  | .alloc ty          => Synth.alloc ctx ty
  | .alloc_array ty e  => Synth.alloc_array ctx ty e
  | .var name          => Synth.var ctx name
  | .dot e field       => Synth.dot ctx e field
  | .arrow e field     => Synth.arrow ctx e field
  | .deref e           => Synth.deref ctx e
  | .index e index     => Synth.index ctx e index

def Synth.unop (ctx : FuncCtx)
               (op : Ast.UnOp)
               (e : Ast.Expr)
               : Synth.ExprResult := do
  let te ← Synth.expr ctx e
  let (op', tau) ←
    match op, te.typ with
    | .int .neg, .prim .int
    | .int .neg, .any         => pure (.int .neg, .prim .int)
    | .int .not, .prim .int
    | .int .not, .any         => pure (.int .not, .prim .int)
    | .bool .neg, .prim .bool
    | .bool .neg, .any        => pure (.bool .neg, .prim .bool)
    | _, _ => throw "Unary operator is not well-typed"
  return ⟨tau, .unop op' te⟩

def Synth.binop (ctx : FuncCtx)
                (op : Ast.BinOp)
                (l r : Ast.Expr)
                : Synth.ExprResult := do
  let l' ← Synth.expr ctx l
  let r' ← Synth.expr ctx r
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
    | .int .rsh   => Synth.binop_type (.prim .int) l'.typ r'.typ
    | .bool .and
    | .bool .or
    | .cmp .lt
    | .cmp .le
    | .cmp .gt
    | .cmp .ge    => Synth.binop_type (.prim .bool) l'.typ r'.typ
    | .cmp .eq
    | .cmp .ne    =>
      if l'.typ = r'.typ
      then pure (.prim .bool)
      else throw "Binary operator is not well-typed"
  return ⟨tau, .binop (Trans.binop op) l' r'⟩

def Synth.ternop (ctx : FuncCtx) (c tt ff : Ast.Expr) : Synth.ExprResult := do
  let c' ← Synth.expr ctx c
  let tt' ← Synth.expr ctx tt
  let ff' ← Synth.expr ctx ff
  if c'.typ ≠ .prim .bool
  then throw "Ternary condition must be a bool"
  else
    let tau ← Synth.intersect_types tt'.typ ff'.typ
    return ⟨tau, .ternop c' tt' ff'⟩

def Synth.app (ctx : FuncCtx)
              (f : Ast.Ident)
              (args : List Ast.Expr)
              : Synth.ExprResult := do
  match ctx.symbols.find? f with
  | some (.func status) =>
    let args' ← args.mapM (Synth.expr ctx)
    let arg_types := args'.map (fun arg => arg.typ)
    let ret_type := -- return unit (i.e. void_star) if there's no return type
      match status.type.ret with
      | some tau => tau
      | none => .void_star
    if arg_types == status.type.args
    then return ⟨ret_type, .app f args'⟩
    else throw "Function argument types don't match"
  | _ => throw "Cannot apply to a non-function type"

def Synth.alloc (ctx : FuncCtx) (tau : Ast.Typ) : Synth.ExprResult := do
  let opt_tau' := Trans.type ctx tau
  match opt_tau' with
  | some tau' => return ⟨.mem (.pointer tau'), .alloc tau'⟩
  | none      => throw s!"Invalid allocation type"

def Synth.alloc_array (ctx : FuncCtx)
                      (tau : Ast.Typ)
                      (e : Ast.Expr)
                      : Synth.ExprResult := do
  let opt_tau' := Trans.type ctx tau
  let e' ← Synth.expr ctx e
  match opt_tau', e'.typ with
  | none, _ => throw s!"Invalid array type"
  | some tau', .prim .int => return ⟨.mem (.array tau'), .alloc_array tau' e'⟩
  | _, _ => throw "Array length must be an integer"

def Synth.var (ctx : FuncCtx) (var : Ast.Ident) : Synth.ExprResult := do
  match ctx.symbols.find? var with
  | some (.var status) =>
    if status.initialised
    then return ⟨status.type, .var var⟩
    else throw s!"Variable {var} not initialised"
  | _ => throw s!"Variable {var} not declared"

def Synth.dot (ctx : FuncCtx)
              (e : Ast.Expr)
              (field : Ast.Ident)
              : Synth.ExprResult := do
  let e' ← Synth.expr ctx e
  match e'.typ with
  | .mem (.pointer <| .mem (.struct name)) =>
    match ctx.structs.find? name with
    | some status =>
      if ¬status.defined
      then throw s!"Struct {name} is not defined"
      else
        match status.fields.find? field with
        | some tau => return ⟨tau, .dot e' field⟩
        | none => throw s!"Invalid field {field}}"
    | none => throw s!"Struct {name} is not defined"
  | _ => throw s!"Arrow operator must be used on a struct pointer"

def Synth.arrow (ctx : FuncCtx)
                (e : Ast.Expr)
                (field : Ast.Ident)
                : Synth.ExprResult := do
  let e' ← Synth.expr ctx e
  match e'.typ with
  | .mem (.struct name) =>
    match ctx.structs.find? name with
    | some status =>
      if ¬status.defined
      then throw s!"Struct {name} is not defined"
      else
        match status.fields.find? field with
        | some tau => return ⟨tau, .dot e' field⟩
        | none => throw s!"Invalid field {field}}"
    | none => throw s!"Struct {name} is not defined"
  | _ => throw s!"Field accessor can only operate on a struct"

def Synth.deref (ctx : FuncCtx) (e : Ast.Expr) : Synth.ExprResult := do
  let e' ← Synth.expr ctx e
  match e'.typ with
  | .mem (.pointer .any) => throw "Cannot dereference a null pointer/function"
  | .mem (.pointer tau)  => return ⟨tau, .deref e'⟩
  | _ => throw "Cannot dereference a non-pointer type"

def Synth.index (ctx : FuncCtx)
                (arr : Ast.Expr)
                (index : Ast.Expr)
                : Synth.ExprResult := do
  let arr' ← Synth.expr ctx arr
  let index' ← Synth.expr ctx index
  match arr'.typ, index'.typ with
  | .mem (.array tau), .prim .int => return ⟨tau, .index arr' index'⟩
  | .mem (.array tau), _ => throw "Array indices must be integers"
  | _, _ => throw "Indexing can only be done on array types"

end
