/- C0deine - Typechecker
   Converts the AST to the TST by dealiasing and annotating expressions with
   types. Any NWT programs are rejected.
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
  let intypes := intypes.map (·.type)
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

structure Result.Core (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool) where
  type    : Typ
  texpr   : Tst.Expr Δ Γ type
  valid   : Tst.Expr.All P texpr

structure Result (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool) where
  calls   : Tst.Calls
  strings : List String
  type    : Typ
  texpr   : Tst.Expr Δ Γ type
  valid   : Tst.Expr.All P texpr

structure Result.List (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool) where
  calls   : Tst.Calls
  strings : List String
  texprs  : List (Result.Core P)


@[inline] def ExprOutput (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool) :=
  Except Error (Result P)

@[inline] def nonvoid (eres : ExprOutput P) : ExprOutput P := do
  let res ← eres
  match res.type with
  | .any => throw <| Error.texpr res.texpr <| s!"Expression cannot be void"
  | _ => return res

@[inline] def small (eres : ExprOutput P) : ExprOutput P := do
  let res ← eres
  if res.type.isSmall then return res
  else throw <| Error.texpr res.texpr <| s!"Expression cannot have large type"

@[inline] def small_nonvoid (eres : ExprOutput P)
    : ExprOutput P := do
   let res ← nonvoid eres
   if res.type.isSmall then return res
   else throw <| Error.texpr res.texpr <| s!"Expression cannot have large type"

mutual
def expr (ctx : FuncCtx)
    (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool)
    (fail : {τ : Typ} → (te : Tst.Expr Δ Γ τ) → ¬P te → Error)
    (exp : Ast.Expr)
    : ExprOutput P := do
  match exp with
  | .num n             =>
    if p : P (.num n)
    then return ⟨ctx.calls, ctx.strings, .prim .int, .num n, .num p⟩
    else throw <| fail (.num n) p
  | .char c            =>
    if p : P (.char c)
    then return ⟨ctx.calls, ctx.strings, .prim .char, .char c, .char p⟩
    else throw <| fail (.char c) p
  | .str s             =>
    let strings' := if s ∉ ctx.strings then s::ctx.strings else ctx.strings
    if p : P (.str s)
    then return ⟨ctx.calls, strings', .prim .string, .str s, .str p⟩
    else throw <| fail (.str s) p
  | .true              =>
    if p : P .true
    then return ⟨ctx.calls, ctx.strings, .prim .bool, .true, .true p⟩
    else throw <| fail .true p
  | .false             =>
    if p : P .false
    then return ⟨ctx.calls, ctx.strings, .prim .bool, .false, .false p⟩
    else throw <| fail .false p
  | .null              =>
    if p : P .null
    then return ⟨ctx.calls, ctx.strings, .mem (.pointer .any), .null, .null p⟩
    else throw <| fail .null p
  | .unop op e         =>
    let res ← small_nonvoid <| expr ctx P fail e
    let op' :=
      match op with
      | .int .neg  => .int .neg
      | .int .not  => .int .not
      | .bool .neg => .bool .neg
    if eq : res.type.equiv op'.type then
      let e' := Tst.Expr.unop op' eq res.texpr
      if p : P e'
      then return ⟨res.calls, res.strings, op'.type, e', .unop res.valid p⟩
      else throw <| fail e' p
    else throw <| Error.expr exp <|
      s!"Unary operator '{op'}' expects type '{op'.type}' but got '{res.type}'"

  | .binop op l r      =>
    let resl ← small_nonvoid <| expr ctx P fail l
    let resr ← small_nonvoid <| expr ctx P fail r
    let calls   := resl.calls.merge resr.calls
    let strings := resl.strings ∪ resr.strings
    -- todo modularize this
    match op with
    | .int iop =>
      let op' := Trans.int_binop iop
      if seq : resl.type = resr.type then
        if leq : resl.type = .prim .int then
          have req := by rw [seq] at leq; exact leq
          let le' := resl.texpr.typeWith (p := fun t => t = .prim .int) leq
          let re' := resr.texpr.typeWith (p := fun t => t = .prim .int) req
          let e' := Tst.Expr.binop_int op' le' re'
          if p : P e' then
            let lvalid : Tst.Expr.All _ le' := resl.valid
            let rvalid : Tst.Expr.All _ re' := resr.valid
            let p' := .binop_int lvalid rvalid p
            return ⟨calls, strings, .prim .int, e', p'⟩
          else throw <| fail e' p
        else throw <| Error.expr exp <|
          s!"Binary operator '{op}' expects type '{Typ.prim .int}' but got '{resl.type}'"
      else throw <| Error.expr exp <|
        s!"Binary operator '{op}' expects both sides to have same type but got '{resl.type}' and '{resr.type}'"

    | .cmp cop =>
      if is_equality : cop.isEquality then
        if eq : resl.type.equiv resr.type then
          if eqtype : resl.type.is_eqtype ∨ resr.type.is_eqtype then
            let le' := resl.texpr
            let re' := resr.texpr
            let e' := Tst.Expr.binop_eq cop is_equality le' re' eq eqtype
            if p : P e' then
              let lvalid : Tst.Expr.All _ le' := resl.valid
              let rvalid : Tst.Expr.All _ re' := resr.valid
              let p' := .binop_eq lvalid rvalid p
              return ⟨calls, strings, .prim .bool, e', p'⟩
            else throw <| fail e' p
          else throw <| Error.expr exp <|
            s!"Binary operator '{op}' cannot compare type '{resl.type}'"
        else throw <| Error.expr exp <|
          s!"Binary operator '{op}' expects both sides to have equivalent types but got '{resl.type}' and '{resr.type}'"
      else
        if eq : resl.type = resr.type then
          if leq : resl.type = .prim .int then
            have req := by rw [eq] at leq; exact leq
            let le' := resl.texpr.intType leq
            let re' := resr.texpr.intType req
            let e' := Tst.Expr.binop_rel₁ cop is_equality le' re'
            if p : P e' then
              let p' := .binop_rel₁ resl.valid resr.valid p
              return ⟨calls, strings, .prim .bool, e', p'⟩
            else throw <| fail e' p
          else
            if leq : resl.type = .prim .char then
              have req := by rw [eq] at leq; exact leq
              let le' := resl.texpr.charType leq
              let re' := resr.texpr.charType req
              let e' := Tst.Expr.binop_rel₂ cop is_equality le' re'
              if p : P e' then
                let p' := .binop_rel₂ resl.valid resr.valid p
                return ⟨calls, strings, .prim .bool, e', p'⟩
              else throw <| fail e' p
            else throw <| Error.expr exp <|
              s!"Binary operator '{op}' expects type '{Typ.prim .int}' or '{Typ.prim .char}' but got '{resl.type}'"
        else throw <| Error.expr exp <|
          s!"Binary operator '{op}' expects both sides to have same type but got '{resl.type}' and '{resr.type}'"

    | .bool bop =>
      let op' := Trans.bool_binop bop
      if leq : resl.type = .prim .bool then
        if req : resr.type = .prim .bool then
          let le' := resl.texpr.boolType leq
          let re' := resr.texpr.boolType req
          let e' := Tst.Expr.binop_bool op' le' re'
          if p : P e' then
            let p' := .binop_bool resl.valid resr.valid p
            return ⟨calls, strings, .prim .bool, e', p'⟩
          else throw <| fail e' p
      throw <| Error.expr exp <|
        s!"Binary operator '{op}' expects both sides to have type '{Typ.prim .bool}' but got '{resl.type}' and '{resr.type}'"

  | .ternop cond tt ff =>
    let resc ← small_nonvoid <| expr ctx P fail cond
    let rest ← small_nonvoid <| expr ctx P fail tt
    let resf ← small_nonvoid <| expr ctx P fail ff
    let calls   := resc.calls.merge rest.calls |>.merge resf.calls
    let strings := resc.strings ∪ rest.strings ∪ resf.strings
    if cbool : resc.type = .prim .bool then
      if eq : rest.type.equiv resf.type then
        let tau' := rest.type.intersect resf.type
        let cc' := resc.texpr.typeWith (p := fun t => t = .prim .bool) cbool
        let e' := .ternop cc' rest.texpr resf.texpr eq
        if p : P e' then
          return ⟨ calls, strings, tau', e'
                 , .ternop resc.valid rest.valid resf.valid p
                 ⟩
        else throw <| fail e' p
      else throw <| Error.expr exp <|
        s!"Ternary true branch has type '{rest.type}' but the false branch has type '{resf.type}'"
    else throw <| Error.expr exp s!"Ternary condition {resc.texpr} must be a bool"

  | .app f args        =>
    match is_func : Γ f with
    | some (.func status) =>
      let resargs ← exprs ctx P fail args
      -- false => not in contract (corrected later if we actually are)
      let calls := resargs.calls.insert f .false

      if len : status.type.arity = resargs.texprs.length then
        let τs := fun (i : Fin status.type.arity) =>
          resargs.texprs.get ⟨↑i, by simp [←len]⟩ |>.type
        let tys_equiv_fn := fun i =>
          (status.type.argTys i).equiv (τs i)
        if tys_equiv : (List.ofFn tys_equiv_fn).all (·) then
          have eq : ∀ i, (status.type.argTys i).equiv
              (τs i) := by
            have := List.all_eq_true.mp tys_equiv
                 |> List.forall_mem_ofFn_iff.mp
            simp [tys_equiv_fn] at this
            simp [τs]
            exact this

          let args_core : (i : Fin status.type.arity) → Result.Core _ :=
            fun i => resargs.texprs.get ⟨↑i, by simp [←len]⟩

          let args : (i : Fin status.type.arity) → Tst.Expr Δ Γ (τs i) :=
            fun i => args_core i |>.texpr

          have valid : (i : Fin status.type.arity) → Tst.Expr.All _ (args i) :=
            fun i => args_core i |>.valid

          let e' := .app f is_func τs eq args
          if p : P e' then
            let p' := .app valid p
            return ⟨calls, resargs.strings, status.type.retTy, e', p'⟩
          else throw <| fail e' p
        else throw <| Error.expr exp <|
          s!"Arguments should have types {List.ofFn status.type.argTys} but received {List.ofFn τs}"
      else throw <| Error.expr exp <|
        s!"Expected {status.type.arity} arguments but received {resargs.texprs.length}"
    | some (.var _) => throw <| Error.expr exp <|
      s!"Cannot call variable {f} (non-function type)"
    | some (.alias _) => throw <| Error.expr exp s!"Cannot call type {f}"
    | none => throw <| Error.expr exp <|
      s!"Cannot call undeclared/undefined function {f}"

  | .alloc tau         =>
    let opt_tau' := Trans.type ctx tau |>.filter (Trans.isSized ctx)
    match opt_tau' with
    | none      => throw <| Error.expr exp s!"Invalid allocation type"
    | some tau' =>
      let e' := .alloc tau'
      if p : P e'
      then return ⟨ctx.calls, ctx.strings, .mem (.pointer tau'), e', .alloc p⟩
      else throw <| fail e' p

  | .alloc_array tau e =>
    let res ← small_nonvoid <| expr ctx P fail e
    let opt_tau' := Trans.type ctx tau |>.filter (Trans.isSized ctx)
    match opt_tau' with
    | none      => throw <| Error.expr exp s!"Invalid array type"
    | some tau' =>
      if eq : res.type = .prim .int then
        let len' := res.texpr.intType eq
        let e' := Tst.Expr.alloc_array tau' len'
        if p : P e' then
          let p' := .alloc_array res.valid p
          return ⟨ctx.calls, ctx.strings, .mem (.array tau'), e', p'⟩
        else throw <| fail e' p
        else throw <| Error.expr exp <|
          s!"Array length expected an '{Typ.prim .int}' but got '{res.type}'"

  | .var name          =>
    match h : Γ name with
    | some (.var status) =>
      if is_init : status.initialised then
        let e' := .var name (by simp [←is_init]; exact h)
        if p : P e'
        then return ⟨ctx.calls, ctx.strings, status.type, e', .var p⟩
        else throw <| fail e' p
      else throw <| Error.expr exp s!"Variable not initialised"
    | _ => throw <| Error.expr exp s!"Variable not declared"

  | .dot e field       =>
    let res ← nonvoid <| expr ctx P fail e
    match eq : res.type with
    | .mem (.struct name) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.texpr res.texpr s!"Struct '{name}' is not defined"
        else
          match status.fields.find? field with
          | some tau =>
            let str := Tst.StructSig.mk status.fields.find?
            have hsig : Δ.struct name = .some str := sorry

            let e' := .dot (res.texpr.structType name eq) field hsig sorry
            if p : P e'
            then return ⟨res.calls, res.strings, tau, e', .dot res.valid p⟩
            else throw <| fail e' p
          | none => throw <| Error.expr exp <|
            s!"Invalid field '{field}' for struct type '{res.type}'"
      | none => throw <| Error.texpr res.texpr s!"Struct '{name}' is not defined"
    | _ => throw <| Error.expr exp <|
      s!"Field accessor expects a struct not type '{res.type}'"

  | .arrow e field     =>
    let res ← expr ctx P fail e
    match eq : res.type with
    | .mem (.pointer <| .mem (.struct name)) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.texpr res.texpr s!"Struct '{name}' is not defined"
        else
          let obj := res.texpr.ptrType (.mem (.struct name)) eq
          if pe : P (.deref obj) then
            let te' := Tst.Expr.deref obj
            have pe' : Tst.Expr.All P te' := by
              simp [te']
              exact .deref res.valid pe

            match status.fields.find? field with
            | some tau =>
              let str := Tst.StructSig.mk status.fields.find?
              have hsig : Δ.struct name = .some str := sorry

              let e' := .dot (te'.structType name (by rfl)) field hsig sorry
              if p : P e'
              then return ⟨res.calls, res.strings, tau, e', .dot pe' p⟩
              else throw <| fail e' p
            | none => throw <| Error.expr exp <|
              s!"Invalid field '{field}' for struct type '{Typ.mem (.struct name)}'"
          else throw <| fail (.deref obj) pe
      | none => throw <| Error.texpr res.texpr s!"Struct '{name}' is not defined"
    | _ => throw <| Error.expr exp <|
      s!"Arrow operator expects a struct pointer not type '{res.type}'"

  | .deref e           =>
    let res ← small <| expr ctx P fail e
    match eq : res.type with
    | .mem (.pointer .any) => throw <| Error.expr e <|
      s!"Cannot dereference a null pointer"
    | .mem (.pointer tau)  =>
      let e' := .deref (res.texpr.ptrType tau eq)
      if p : P e'
      then return ⟨res.calls, res.strings, tau, e', .deref res.valid p⟩
      else throw <| fail e' p
    | _ => throw <| Error.expr e <|
      s!"Cannot dereference a non-pointer type '{res.type}'"

  | .index arr indx    =>
    let resa ← small_nonvoid <| expr ctx P fail arr
    let resi ← small_nonvoid <| expr ctx P fail indx
    let calls   := resa.calls.merge resi.calls
    let strings := resa.strings ∪ resi.strings
    match aeq : resa.type with
    | .mem (.array tau) =>
      if ieq : resi.type = .prim .int then
        let e' := .index (resa.texpr.arrType tau aeq) (resi.texpr.intType ieq)
        if p : P e'
        then return ⟨calls, strings, tau, e', .index resa.valid resi.valid p⟩
        else throw <| fail e' p
      else throw <| Error.expr exp <|
      s!"Array indices must be type '{Typ.prim .int}' not type '{resi.type}'"
    | _ => throw <| Error.expr exp <|
      s!"Array indexing must be on array types not type '{resa.type}'"

  | .result           =>
    match ctx.ret_type with
    | .some tau =>
      if p : P (τ := tau) .result
      then return ⟨ctx.calls, ctx.strings, tau, .result, .result p⟩
      else throw <| fail .result p
    | .none     => throw <| Error.expr exp <|
      s!"Cannot use result when function's return type is void"

  | .length e         =>
    let res ← small_nonvoid <| expr ctx P fail e
    match eq : res.type with
    | .mem (.array tau) =>
      let e' := .length (res.texpr.arrType tau eq)
      if p : P e' then
        return ⟨res.calls, res.strings, .prim .int, e', .length res.valid p⟩
      else throw <| fail e' p
    | _ => throw <| Error.expr exp <|
      s!"Can only check the length of arrays not of type '{res.type}'"

def exprs (ctx : FuncCtx)
          (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool)
          (fail : {τ : Typ} → (te : Tst.Expr Δ Γ τ) → ¬P te → Error)
          (exps : List Ast.Expr)
          : Except Error (Result.List P) := do
  match exps with
  | [] => return ⟨ctx.calls, ctx.strings, []⟩
  | e :: es =>
    let rese ← small_nonvoid <| expr ctx P fail e
    let reses ← exprs ctx P fail es
    let calls   := rese.calls.merge reses.calls
    let strings := rese.strings ∪ reses.strings
    let texprs  := ⟨rese.type, rese.texpr, rese.valid⟩ :: reses.texprs
    return ⟨calls, strings, texprs⟩
end

end Synth.Expr

namespace Synth.LValue

structure Result (Δ : Tst.GCtx) (Γ : Tst.FCtx) where
  calls : Tst.Calls
  type : Typ
  lval : Tst.LValue Δ Γ type

def small (res : Except Error (Result Δ Γ)) : Except Error (Result Δ Γ) := do
  if (← res).type.isSmall
  then return (← res)
  else throw <| Error.msg s!"LValue has large type"

def lvalue (ctx : FuncCtx) (lval : Ast.LValue) : Except Error (Result Δ Γ) := do
  match lval with
  | .var var =>
    match h : Γ var with
    | some (.var status) =>
      if is_init : status.initialised then
        let lv' := .var var (by simp [←is_init]; exact .inl h)
        return ⟨ctx.calls, status.type, lv'⟩
      else throw <| Error.lval lval s!"Variable not initialised"
    | _ => throw <| Error.lval lval s!"Variable not declared"

  | .dot lv field =>
    let res ← lvalue ctx lv
    match tyeq : res.type with
    | .mem (.struct name) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.lval lval s!"Struct '{name}' is not defined"
        else
          match h : status.fields.find? field with
          | some tau =>
            let str := Tst.StructSig.mk status.fields.find?
            have hsig : Δ.struct name = .some str := sorry

            let lv' := .dot (res.lval.structType name tyeq) field hsig h
            return ⟨res.calls, tau, lv'⟩
          | none => throw <| Error.lval lval <|
            s!"Invalid field '{field}' for struct type '{res.type}'"
      | none => throw <| Error.lval lval s!"Struct {name} is not defined"
    | _ => throw <| Error.lval lval <|
      s!"Field accessor expects a struct not type '{res.type}'"

  | .arrow lv field =>
    let res ← lvalue ctx lv
    match tyeq : res.type with
    | .mem (.pointer <| .mem (.struct name)) =>
      match ctx.structs.find? name with
      | some status =>
        if ¬status.defined
        then throw <| Error.lval lval s!"Struct '{name}' is not defined"
        else
          match h : status.fields.find? field with
          | some tau =>
            let str := Tst.StructSig.mk status.fields.find?
            have hsig : Δ.struct name = .some str := sorry

            let dref' : Tst.LValue Δ Γ _ :=
              .deref (res.lval.ptrType (.mem (.struct name)) tyeq)
            let lv' := .dot (dref'.structType name (by rfl)) field hsig h
            return ⟨res.calls, tau, lv'⟩
          | none => throw <| Error.lval lval <|
            s!"Invalid field '{field}' for struct type '{res.type}'"
      | none => throw <| Error.lval lval s!"Struct '{name}' is not defined"
    | _ => throw <| Error.lval lval <|
      s!"Arrow operator expects a struct pointer not type '{res.type}'"

  | .deref lv =>
    let res ← lvalue ctx lv
    match tyeq : res.type with
    | .mem (.pointer tau)  =>
      return ⟨res.calls, tau, .deref (res.lval.ptrType tau tyeq)⟩
    | _ => throw <| Error.lval lval <|
      s!"Cannot dereference a non-pointer type '{res.type}'"

  | .index arr indx =>
    let resa ← lvalue ctx arr
    let resi ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract indx
    let calls := resa.calls.merge resi.calls
    match tya_eq : resa.type, tyi_eq : resi.type with
    | .mem (.array tau), .prim .int =>
      let indx' := ⟨resi.texpr.intType tyi_eq, resi.valid⟩
      let lv' := .index (resa.lval.arrType tau tya_eq) indx'
      return ⟨calls, tau, lv'⟩
    | .mem (.array _tau), _ => throw <| Error.lval lval <|
      s!"Array indices must be type '{Typ.prim .int}' not type '{resi.type}'"
    | _, _ => throw <| Error.lval lval <|
      s!"Array indexing must be on array types not type '{resa.type}'"

end Synth.LValue

namespace Synth.Anno

def func (ctx : FuncCtx) (as : List Ast.Anno)
    : Except Error (FuncCtx × List (Tst.Anno.Function Δ Γ)) := do
  match as with
  | []                  => return (ctx, [])
  | .requires e :: rest =>
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_result Error.no_result e
    if tyeq : res.type = .prim .bool then
      let calls' := ctx.calls.merge (res.calls.mapVal (fun _ _ => true))
      let (ctx', rest') ← func {ctx with calls := calls'} rest
      let e' := ⟨res.texpr.boolType tyeq, res.valid⟩
      return ⟨ctx', ⟨.requires e', by simp⟩ :: rest'⟩
    else
      throw <| Error.expr e <|
        s!"Requires must have type {Typ.prim .bool} not type '{res.type}'"

  | .ensures  e :: rest =>
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx (fun _ => true) (fun _ np => by simp at np) e
    if tyeq : res.type = .prim .bool then
      let calls' := ctx.calls.merge (res.calls.mapVal (fun _ _ => true))
      let (ctx', rest') ← func {ctx with calls := calls'} rest
      return ⟨ctx', ⟨.ensures (res.texpr.boolType tyeq), by simp⟩ :: rest'⟩
    else
      throw <| Error.expr e <|
        s!"Ensures must have type {Typ.prim .bool} not type '{res.type}'"

  | .loop_invar _ :: _ =>
    throw <| Error.msg "Loop invariants can only precede loop bodies"
  | .assert _ :: _ =>
    throw <| Error.msg "Assert cannot annotate functions"

def loop (ctx : FuncCtx) (as : List Ast.Anno)
    : Except Error (FuncCtx × List (Tst.Anno.Loop Δ Γ)) := do
  match as with
  | []            => return (ctx, [])
  | .requires _   :: _    => throw <| Error.msg "Requires can only annotate functions"
  | .ensures  _   :: _    => throw <| Error.msg "Ensures can only annotate functions"
  | .loop_invar e :: rest =>
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_result Error.no_result e
    if tyeq : res.type = .prim .bool then
      let calls' := ctx.calls.merge (res.calls.mapVal (fun _ _ => true))
      let (ctx', rest') ← loop {ctx with calls := calls'} rest
      let e' := ⟨res.texpr.boolType tyeq, res.valid⟩
      return (ctx', ⟨.loop_invar e', by simp⟩ :: rest')
    else
      throw <| Error.expr e <|
        s!"Loop invariants must have type {Typ.prim .bool} not type '{res.type}'"

  | .assert _ :: _       => throw <| Error.msg "Assert cannot annotate loops"

def free (ctx : FuncCtx) (a : Ast.Anno)
    : Except Error (FuncCtx × (Tst.Anno.Free Δ Γ)) := do
  match a with
  | .requires _   => throw <| Error.msg "Requires can only annotate functions"
  | .ensures  _   => throw <| Error.msg "Ensures can only annotate functions"
  | .loop_invar _ =>
    throw <| Error.msg "Loop invariants can only precede loop bodies"
  | .assert e =>
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_result Error.no_result e
    if tyeq : res.type = .prim .bool then
      let calls' := ctx.calls.merge (res.calls.mapVal (fun _ _ => true))
      return ⟨{ctx with calls := calls'},
        ⟨.assert ⟨res.texpr.boolType tyeq, res.valid⟩, by simp⟩
      ⟩
    else
      throw <| Error.expr e <|
        s!"Assert must have type {Typ.prim .bool} not type '{res.type}'"

end Synth.Anno

namespace Stmt

structure Result (Δ : Tst.GCtx) (Γ : Tst.FCtx) (ρ : Option Typ) where
  ctx  : FuncCtx
  stmt : Tst.Stmt Δ Γ ρ

structure Result.List (Δ : Tst.GCtx) (Γ : Tst.FCtx) (ρ : Option Typ) where
  ctx   : FuncCtx
  stmts : Tst.Stmt.List Δ Γ ρ

@[inline] private def wrapError
    (stmt : Ast.Stmt)
    (res : Except Error α)
    : Except Error α :=
  res.tryCatch (fun err => throw {err with statement := some stmt})

mutual
def stmt (ctx : FuncCtx) (stm : Ast.Stmt) : Except Error (Result Δ Γ ρ) := do
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
        match init with
        | none =>
          let Γ' := Γ.updateVar name ⟨tau, false⟩
          let res ← stmts (Γ := Γ')
              {ctx' with calls := ctx.calls, strings := ctx.strings} body
          let symbols' := -- restore old symbol status
            match ctx.symbols.find? name with
            | some status => res.ctx.symbols.insert name status
            | none => res.ctx.symbols.erase name
          let calledOldCtx := { res.ctx with symbols := symbols' }
          let name' : Typ.Typed Symbol := ⟨tau, name⟩

          return ⟨calledOldCtx, .decl name' (by simp) res.stmts⟩

        | some e =>
          let res_init ← handle <| Synth.Expr.small_nonvoid <|
            Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
          -- types must be equivalent on both sides
          if ty_equiv : tau.equiv res_init.type then
            let init' := ⟨res_init.texpr, res_init.valid⟩

            -- if we are assigning something to struct type, must be defined
            if let Typ.mem (.struct sname) := res_init.type then
              match ctx.structs.find? sname with
              | some status =>
                if ¬ status.defined then throw <| Error.stmt stm <|
                  s!"Expression '{res_init.texpr}' has undefined type '{res_init.type}'"
              | _ => throw <| Error.stmt stm <|
                s!"Expression '{res_init.texpr}' has undefined/undeclared type '{res_init.type}'"

            let Γ' := Γ.updateVar name ⟨tau, true⟩
            let calls := res_init.calls.merge ctx'.calls
            let strings := res_init.strings ∪ ctx'.strings
            let res ← stmts (Γ := Γ') {ctx' with calls, strings} body
            let symbols' := -- restore old symbol status
              match ctx.symbols.find? name with
              | some status => res.ctx.symbols.insert name status
              | none => res.ctx.symbols.erase name
            let calledOldCtx := { res.ctx with symbols := symbols' }
            let name' := ⟨tau, name⟩
            let stmt' :=
              .decl_init name' init' (by simp; exact ty_equiv) (by simp)
                res.stmts
            return ⟨calledOldCtx, stmt'⟩
          else throw <| Error.stmt stm <|
            s!"Variable '{name}' has mismatched types. Declaration expects '{tau}' but {res_init.texpr} has type '{res_init.type}'"

  | .assn_var var e body =>
    match h : Γ var with
    | none => throwS s!"Variable '{var}' must be declared before assignment"
    | some (.var vstatus) =>
      let res ← handle <| Synth.Expr.small_nonvoid <|
          Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
      let ctx := {ctx with calls := res.calls, strings := res.strings}

      if ty_equiv : vstatus.type.equiv res.type then
        let Γ' := Γ.updateVar var ⟨vstatus.type, true⟩
        let ctx' :=
          if vstatus.initialised then ctx else
            let symbols' :=
              ctx.symbols.insert var (.var ⟨vstatus.type, true⟩)
            { ctx with symbols := symbols' }

        let lv' := Tst.LValue.var (τ := vstatus.type) var (by
            if init : vstatus.initialised
            then simp [←init]; exact .inl h
            else simp at init; simp [←init]; exact .inr h
          )
        let e' : Tst.Expr.NoContract Δ Γ _ := ⟨res.texpr, res.valid⟩

        let res ← stmts (Γ := Γ') ctx' body

        let stmt' :=
          .assign_var lv' (by simp [lv']; rfl) e' (ty_equiv) (by simp) res.stmts
        return ⟨res.ctx, stmt'⟩
      else throwS s!"Assignment of '{var}' expects type '{vstatus.type}' but got '{res.type}'"
    | some (.func _)  => throwS s!"Cannot assign to function '{var}'"
    | some (.alias _) => throwS s!"Cannot assign to type alias '{var}'"

  | .assn lv op h e =>
    let resl ← handleLV <| Synth.LValue.small <| Synth.LValue.lvalue ctx lv
    let resr ← handle <| Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
    let ctx := { ctx with calls := resl.calls.merge resr.calls
                        , strings := resr.strings
                }
    match op_eq : op with
    | .eq =>
      if ty_equiv : resl.type.equiv resr.type then
        have : ∀ name h, resl.lval ≠ .var name h := by
          intro b name h'
          simp [op_eq] at h
          sorry
        return ⟨ctx, .assign resl.lval this ⟨resr.texpr, resr.valid⟩ ty_equiv⟩
      else throwS s!"Left side of assignment has type '{resl.type}' doesn't match the right side '{resr.type}'"
    | .aseq binop =>
      if l_eq : resl.type = .prim .int then
        if r_eq : resr.type = .prim .int then
          let lv' := resl.lval.intType l_eq
          let e'  := ⟨resr.texpr.intType r_eq, resr.valid⟩
          let stmt' := .asnop lv' (Trans.int_binop binop) e'
          return ⟨ctx, stmt'⟩
        else throwS s!"Assignment with operations must have type '{Typ.prim .int}' but right side is '{resr.type}'"
      else throwS s!"Assignment with operations must have type '{Typ.prim .int}'  but left side is '{resl.type}'"

  | .ite cond tt ff =>
    let resc ← handle <| Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract cond
    let ctx' := {ctx with calls := resc.calls, strings := resc.strings}
    match c_eq : resc.type with
    | .prim .bool =>
      let ⟨ctx1, tt'⟩ ← stmts ctx' tt
      let ⟨ctx2, ff'⟩ ← stmts ctx' ff
      let cond' := ⟨resc.texpr.boolType c_eq, resc.valid⟩
      return ⟨ctx1.join ctx2, .ite cond' tt' ff'⟩
    | _ => throwS s!"If condition must be of type '{Typ.prim .bool}' not '{resc.type}'"

  | .while cond annos body =>
    let resc ← handle <| Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract cond
    let (ctx', annos') ← handleAnnos <| Synth.Anno.loop ctx annos
    match c_eq : resc.type with
    | .prim .bool =>
      let ⟨ctx'', body'⟩ ←
        stmts ctx' body
      let cond' := ⟨resc.texpr.boolType c_eq, resc.valid⟩
      let ctx''' :=
        { ctx with calls   := ctx''.calls.merge resc.calls
                 , strings := ctx''.strings ∪ resc.strings
        }
      return ⟨ctx''', .while cond' annos' body'⟩
    | _ => throwS s!"Loop condition must be of type '{Typ.prim .bool}' not '{resc.type}'"

  | .return .none =>
    match ρ with
    | some _ => throw <| Error.stmt stm <|
        s!"Expected return type is '{ctx.ret_type}'" -- todo change this msg?
    | none =>
      return ⟨{ctx with returns := true}, .return_void⟩

  | .return (.some e) =>
    match ρ with
    | none => throw <| Error.stmt stm <|
        s!"Expected return type is '{ctx.ret_type}'" -- todo change this msg?
    | some τ =>
      let res ← handle <| Synth.Expr.small_nonvoid <|
        Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
      if tyeq : res.type = τ then
        let e' : Tst.Expr.NoContract Δ Γ _ :=
          ⟨res.texpr.typeWithEq tyeq, res.valid⟩

        let symbols' := ctx.symbols.mapVal (fun _ status =>
            match status with
            | .var vstatus => Status.Symbol.var {vstatus with initialised := true}
            | _ => status
          )
        let calls := ctx.calls.merge res.calls
        let strings := ctx.strings ∪ res.strings
        let ctx' := { ctx with symbols := symbols'
                             , returns := true
                             , calls
                             , strings
                    }
        return ⟨ctx', .return_tau e'⟩
      else throw <| Error.stmt stm <|
        s!"Expected return type was '{ctx.ret_type}' but got '{res.type}'"

  | .assert e =>
    let res ← handle <| Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
    match tyeq : res.type with
    | .prim .bool =>
      let e'   := ⟨res.texpr.boolType tyeq, res.valid⟩
      let ctx' := { ctx with calls := res.calls, strings := res.strings }
      return ⟨ctx', .assert e'⟩
    | _ => throwS s!"Assert condition must be of type '{Typ.prim .bool}' not '{res.type}'"

  | .error e =>
    let res ← handle <| Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
    match tyeq : res.type with
    | .prim .string =>
      let e' := ⟨res.texpr.stringType tyeq, res.valid⟩

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
      return ⟨ctx', .error e'⟩
    | _ => throwS s!"Error condition must be of type '{Typ.prim .string}' not '{res.type}'"

  | .exp e =>
    let res ← handle <| Synth.Expr.small <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
    let e'   := ⟨res.texpr, res.valid⟩
    let ctx' := {ctx with calls := res.calls, strings := res.strings}
    return ⟨ctx', .expr e'⟩

  | .anno a =>
    let (ctx', a') ← handleAnno <| Synth.Anno.free ctx a
    return ⟨ctx', .anno a'⟩

def stmts (ctx : FuncCtx)
          (body : List Ast.Stmt)
          : Except Error (Result.List Δ Γ ρ) := do
  match body with
  | [] => return ⟨ctx, .nil⟩
  | b::bs =>
    let resb ← stmt ctx b
    /- We need to typecheck after returns but we disregard the result.
       TOOD: think about how this could be structurally enforced.
     -/
    if resb.ctx.returns then
      let Γ' := Γ.initialiseAll
      let resbs : (Result.List Δ Γ' ρ) ← stmts (Γ := Γ') resb.ctx bs
      return ⟨resbs.ctx, .cons resb.stmt .nil⟩
    else
      let resbs ← stmts resb.ctx bs
      return ⟨resbs.ctx, .cons resb.stmt resbs.stmts⟩
end

end Stmt

namespace Global

structure Result (Δ : Tst.GCtx) where
  ctx    : GlobalCtx
  Δ'     : Tst.GCtx
  gdecl? : Option (Tst.GDecl Δ Δ')

structure Result.List (Δ : Tst.GCtx) where
  ctx    : GlobalCtx
  Δ'     : Tst.GCtx
  gdecls : (Tst.GDecl.List Δ Δ')

-- def Result := Except Error (GlobalCtx × Option Tst.GDecl)
-- deriving Inhabited

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

def fdecl (extern : Bool) (ctx : GlobalCtx) (f : Ast.FDecl)
    : Except Error (Result Δ) := do
  if extern && Symbol.main == f.name
  then throw <| Error.func f.name <|
    s!"Function 'main' cannot appear in headers"
  else
    let (ctx', fctx, ret) ← func ctx extern false f.name f.type f.params
    let params ← Trans.params fctx f.params
    let init_Γ := Tst.FCtx.init Δ params
    let (fctx', annos) ← Synth.Anno.func (Γ := init_Γ) fctx f.annos
    let fdecl := Tst.GDecl.fdecl {ret, name := f.name, params, annos}
    return ⟨{ctx' with calls := ctx'.calls.merge fctx'.calls}, _, some fdecl⟩

def fdef (extern : Bool) (ctx : GlobalCtx) (f : Ast.FDef)
    : Except Error (Result Δ) := do
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
    let retTy := Typ.flattenOpt ret
    let init_Γ := Tst.FCtx.init Δ params
    let (fctx', annos) ← Synth.Anno.func (Γ := init_Γ) fctx f.annos
    let fdecl := {ret, name := f.name, params, init_Γ, annos}

    let ⟨fctx'', body'⟩ ←
      Stmt.stmts (Δ := Δ) (Γ := init_Γ.addFunc f.name retTy params) (ρ := ret) fctx' f.body
        |>.tryCatch (fun err => throw {err with function := some f.name})

    if ¬(ret.isNone || fctx''.returns)
    then throw <| Error.func f.name <|
        s!"Function does not return on some paths"

    let body'' :=
      if ret_none : none = ret then
        body'.toList.append
          [cast (by simp [ret_none]; rfl) Tst.Stmt.return_void]
      else body'.toList

    let funcCalls := ctx'.funcCalls.insert f.name fctx''.calls
    let calls     := ctx'.calls.merge fctx''.calls
    let strings   := ctx'.strings ∪ fctx''.strings

    let fdef := Tst.GDecl.fdef ⟨fdecl, body''⟩
    return ⟨{ctx' with calls, funcCalls, strings}, _, some fdef⟩

def tydef (ctx : GlobalCtx) (t : Ast.TyDef) : Except Error (Result Δ) := do
  let tau' ←
    match Trans.type ctx t.type with
    | some tau => pure tau
    | none => throw <| Error.msg <| s!"'{t}' must have a non-void, known type"
  let ctx' ← Validate.typedef ctx t.name tau'
  return ⟨ctx', Δ, none⟩

def sdecl (ctx : GlobalCtx) (s : Ast.SDecl) : Except Error (Result Δ) := do
  let structs' :=
    match ctx.structs.find? s.name with
    | none =>
      ctx.structs.insert s.name ⟨Std.HashMap.empty, false⟩
    | some _ => ctx.structs
  return ⟨{ctx with structs := structs'}, Δ, none⟩

def sdef (ctx : GlobalCtx) (s : Ast.SDef) : Except Error (Result Δ) := do
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
  return ⟨{ctx with structs := structs'}, _, some (.sdef ⟨s.name, fields'⟩)⟩

def gdec (extern : Bool) (ctx : GlobalCtx) (g : Ast.GDecl)
    : Except Error (Result Δ) := do
  match g with
  | .fdecl f => fdecl extern ctx f
  | .fdef  f => fdef extern ctx f
  | .tydef t => tydef ctx t
  | .sdecl s => sdecl ctx s
  | .sdef  s => sdef ctx s

def gdecs (extern : Bool) (acc : Result.List Δ) (g : Ast.GDecl)
    : Except Error (Result.List Δ) := do
  let res ← Global.gdec (Δ := acc.Δ') extern acc.ctx g
  match res.gdecl? with
  | none    => return ⟨res.ctx, res.Δ', .update acc.gdecls⟩
  | some g' => return ⟨res.ctx, res.Δ', .cons acc.gdecls g'⟩

end Global

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
