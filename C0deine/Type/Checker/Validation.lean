/- C0deine - Type.Checker.Validation
   Some simple translations and validations for results
   - Thea Brick
 -/
import C0deine.Type.Checker.Context

namespace C0deine.Typechecker

def Trans.type [Ctx α] (ctx : α) : Ast.Typ → Option Typ
  | .int    => some <| .prim .int
  | .bool   => some <| .prim .bool
  | .char   => some <| .prim .char
  | .string => some <| .prim .string
  | .tydef name =>
    match (Ctx.symbols ctx).get? name with
    | some (.alias tau) => some tau
    | _ => none
  | .ptr (tau : Ast.Typ) => Trans.type ctx tau |>.map (.mem ∘ .pointer)
  | .arr (tau : Ast.Typ) => Trans.type ctx tau |>.map (.mem ∘ .array)
  | .struct name => some <| .mem (.struct name)

def Trans.isSized [Ctx α] (ctx : α) : Typ → Bool
  | .mem (.struct name) =>
    match (Ctx.structs ctx).get? name with
    | some status => status.defined
    | none => false
  | _ => true

@[inline] def Trans.int_binop : Ast.BinOp.Int → Tst.BinOp.Int
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

@[inline] def Trans.bool_binop : Ast.BinOp.Bool → Tst.BinOp.Bool
  | .and => .and
  | .or  => .or

@[inline] def Trans.binop : Ast.BinOp → Tst.BinOp
  | .int op             => .int (Trans.int_binop op)
  | .bool op            => .bool (Trans.bool_binop op)
  | .cmp .less          => .cmp .less
  | .cmp .greater       => .cmp .greater
  | .cmp .equal         => .cmp .equal
  | .cmp .not_equal     => .cmp .not_equal
  | .cmp .less_equal    => .cmp .less_equal
  | .cmp .greater_equal => .cmp .greater_equal

def Trans.params (ctx : FuncCtx)
                 (params : List Ast.Param)
                 : Except Error (List (Typ.Typed Symbol)) :=
  params.foldrM (fun p acc =>
    match Trans.type ctx p.type with
    | some ty => pure (⟨ty, p.name⟩ :: acc)
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
    match ctx.symbols.get? var with
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
  let intypes := intypes.map (·.type)
  let status := .func ⟨⟨output, intypes⟩, extern || defining⟩
  let symbols' := fctx.symbols.insert name status
  let fctx ← Validate.params {fctx with symbols := symbols'} inputs
  if ¬(output.all Typ.isSmall)
  then throw <| Error.func name <|
    s!"Function has non-small output type '{output}'"
  else
    match ctx.symbols.get? name with
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
    match ctx.symbols.get? name with
    | some (.func status) =>
      if status.defined
      then return ()
      else if name = main
      then throw <| Error.msg s!"Function 'main' must be defined"
      else err name
    | _ => err name
  ) ()
