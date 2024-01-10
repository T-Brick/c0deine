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

-- todo remove duplication
structure Result.Core
    (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool)
    (init_set : Tst.Initialised.Acc)
where
  type  : Typ
  texpr : Tst.Expr Δ Γ type
  valid : Tst.Expr.All P texpr
  init  : Tst.Initialised.Expr texpr init_set

structure Result
    (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool)
    (init_set : Tst.Initialised.Acc)
where
  calls   : Tst.Calls
  strings : List String
  type    : Typ
  texpr   : Tst.Expr Δ Γ type
  valid   : Tst.Expr.All P texpr
  init    : Tst.Initialised.Expr texpr init_set

structure Result.List
    (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool)
    (init_set : Tst.Initialised.Acc)
where
  calls   : Tst.Calls
  strings : List String
  texprs  : List (Result.Core P init_set)


@[inline] def ExprOutput
    (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool)
    (init_set : Tst.Initialised.Acc) :=
  Except Error (Result P init_set)

@[inline] def nonvoid
    (eres : ExprOutput P init_set) : ExprOutput P init_set := do
  let res ← eres
  match res.type with
  | .any => throw <| Error.texpr res.texpr <| s!"Expression cannot be void"
  | _ => return res

@[inline] def small (eres : ExprOutput P init_set) : ExprOutput P init_set := do
  let res ← eres
  if res.type.isSmall then return res
  else throw <| Error.texpr res.texpr <| s!"Expression cannot have large type"

@[inline] def small_nonvoid
    (eres : ExprOutput P init_set) : ExprOutput P init_set := do
   let res ← nonvoid eres
   if res.type.isSmall then return res
   else throw <| Error.texpr res.texpr <| s!"Expression cannot have large type"

mutual
def expr (ctx : FuncCtx)
    {init_set : Tst.Initialised.Acc}
    (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool)
    (fail : {τ : Typ} → (te : Tst.Expr Δ Γ τ) → ¬P te → Error)
    (exp : Ast.Expr)
    : ExprOutput P init_set := do
  match exp with
  | .num n             =>
    if p : P (.num n) then
      have p' := .num (by simp; exact p)
      have e'_init := .num (by simp)
      return ⟨ctx.calls, ctx.strings, .prim .int, .num n, p', e'_init⟩
    else throw <| fail (.num n) p

  | .char c            =>
    if p : P (.char c) then
      have p' := .char (by simp; exact p)
      have e'_init := .char (by simp)
      return ⟨ctx.calls, ctx.strings, .prim .char, .char c, p', e'_init⟩
    else throw <| fail (.char c) p

  | .str s             =>
    let strings' := if s ∉ ctx.strings then s::ctx.strings else ctx.strings
    if p : P (.str s) then
      have p' := .str (by simp; exact p)
      have e'_init := .str (by simp)
      return ⟨ctx.calls, strings', .prim .string, .str s, p', e'_init⟩
    else throw <| fail (.str s) p

  | .true              =>
    if p : P .true then
      have p' := .true (by simp; exact p)
      have e'_init := .true (by simp)
      return ⟨ctx.calls, ctx.strings, .prim .bool, .true, p', e'_init⟩
    else throw <| fail .true p

  | .false             =>
    if p : P .false then
      have p' := .false (by simp; exact p)
      have e'_init := .false (by simp)
      return ⟨ctx.calls, ctx.strings, .prim .bool, .false, p', e'_init⟩
    else throw <| fail .false p

  | .null              =>
    if p : P .null then
      have p' := .null (by simp; exact p)
      have e'_init := .null (by simp)
      return ⟨ctx.calls, ctx.strings, .mem (.pointer .any), .null, p', e'_init⟩
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
      if p : P e' then
        have p' := .unop res.valid (by simp; exact p)
        have e'_init := .unop res.init (by simp)
        return ⟨res.calls, res.strings, op'.type, e', p', e'_init⟩
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
            let p' := .binop_int lvalid rvalid (by simp; exact p)
            have e'_init := .binop_int resl.init resr.init (by simp)
            return ⟨calls, strings, .prim .int, e', p', e'_init⟩
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
              let p' := .binop_eq lvalid rvalid (by simp; exact p)
              have e'_init := .binop_eq resl.init resr.init (by simp)
              return ⟨calls, strings, .prim .bool, e', p', e'_init⟩
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
              let p' := .binop_rel₁ resl.valid resr.valid (by simp; exact p)
              have e'_init := .binop_rel₁ resl.init resr.init (by simp)
              return ⟨calls, strings, .prim .bool, e', p', e'_init⟩
            else throw <| fail e' p
          else
            if leq : resl.type = .prim .char then
              have req := by rw [eq] at leq; exact leq
              let le' := resl.texpr.charType leq
              let re' := resr.texpr.charType req
              let e' := Tst.Expr.binop_rel₂ cop is_equality le' re'
              if p : P e' then
                let p' := .binop_rel₂ resl.valid resr.valid (by simp; exact p)
                have e'_init := .binop_rel₂ resl.init resr.init (by simp)
                return ⟨calls, strings, .prim .bool, e', p', e'_init⟩
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
            let p' := .binop_bool resl.valid resr.valid (by simp; exact p)
            have e'_init := .binop_bool resl.init resr.init (by simp)
            return ⟨calls, strings, .prim .bool, e', p', e'_init⟩
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
          have p' := .ternop resc.valid rest.valid resf.valid (by simp; exact p)
          have e'_init := .ternop resc.init rest.init resf.init (by simp)
          return ⟨calls, strings, tau', e', p', e'_init⟩
        else throw <| fail e' p
      else throw <| Error.expr exp <|
        s!"Ternary true branch has type '{rest.type}' but the false branch has type '{resf.type}'"
    else throw <| Error.expr exp s!"Ternary condition {resc.texpr} must be a bool"

  | .app f args        =>
    match is_func : Γ f with
    | some (.func status) =>
      let resargs ← exprs ctx init_set P fail args
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

          let args_core : (i : Fin status.type.arity) → Result.Core _ _ :=
            fun i => resargs.texprs.get ⟨↑i, by simp [←len]⟩

          let args : (i : Fin status.type.arity) → Tst.Expr Δ Γ (τs i) :=
            fun i => args_core i |>.texpr

          have valid : (i : Fin status.type.arity) → Tst.Expr.All _ (args i) :=
            fun i => args_core i |>.valid

          have init : (i : Fin status.type.arity)
                    → Tst.Initialised.Expr (args i) _ :=
            fun i => args_core i |>.init

          let e' := .app f is_func τs eq args
          if p : P e' then
            let p' := .app valid (by simp; exact p)
            have e'_init := .app init (by simp)
            return ⟨calls, resargs.strings, status.type.retTy, e', p', e'_init⟩
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
      if p : P e' then
        have p' := .alloc (by simp; exact p)
        have e'_init := .alloc (by simp)
        return ⟨ctx.calls, ctx.strings, .mem (.pointer tau'), e', p', e'_init⟩
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
          let p' := .alloc_array res.valid (by simp; exact p)
          have e'_init := .alloc_array res.init (by simp)
          return ⟨ctx.calls, ctx.strings, .mem (.array tau'), e', p', e'_init⟩
        else throw <| fail e' p
        else throw <| Error.expr exp <|
          s!"Array length expected an '{Typ.prim .int}' but got '{res.type}'"

  | .var name          =>
    match h : Γ name with
    | some (.var tau) =>
      match is_init : init_set name with
      | true =>
          let e' := .var name h
          if p : P e' then
            have p' := .var (by simp; exact p)
            have e'_init :=
              .var (by simp [Tst.Initialised.expr]; exact is_init)
            return ⟨ctx.calls, ctx.strings, tau, e', p', e'_init⟩
          else throw <| fail e' p
      | false => throw <| Error.expr exp s!"Variable not initialised"
    | _ => throw <| Error.expr exp s!"Variable not declared"

  | .dot e field       =>
    let res ← nonvoid <| expr ctx P fail e
    match eq : res.type with
    | .mem (.struct name) =>
      match hsig : Δ.struct name with
      | some status =>
        if defined : status.defined then
          match f_ty : status.fields field with
          | some tau =>
            let e' :=
              .dot (res.texpr.structType name eq) field
                (by rw [←defined]; exact hsig) f_ty
            if p : P e' then
              have p' := .dot res.valid (by simp; exact p)
              have e'_init := .dot res.init (by simp)
              return ⟨res.calls, res.strings, tau, e', p', e'_init⟩
            else throw <| fail e' p
          | none => throw <| Error.expr exp <|
            s!"Invalid field '{field}' for struct type '{res.type}'"
        else throw <| Error.texpr res.texpr s!"Struct '{name}' is not defined"
      | none => throw <| Error.texpr res.texpr s!"Struct '{name}' is not defined"
    | _ => throw <| Error.expr exp <|
      s!"Field accessor expects a struct not type '{res.type}'"

  | .arrow e field     =>
    let res ← expr ctx P fail e
    match eq : res.type with
    | .mem (.pointer <| .mem (.struct name)) =>
      match hsig : Δ.struct name with
      | some status =>
        if defined : status.defined then
          let obj := res.texpr.ptrType (.mem (.struct name)) eq
          if pe : P (.deref obj) then
            let te' := Tst.Expr.deref obj         -- todo better names
            have pe' : Tst.Expr.All P te' := by
              simp [te']
              exact .deref res.valid (by simp; exact pe)
            have pe'_init : Tst.Initialised.Expr te' init_set := by
              simp [te']
              exact .deref res.init (by simp)

            match f_ty : status.fields field with
            | some tau =>
              let e' :=
                .dot (te'.structType name (by rfl)) field
                  (by rw [←defined]; exact hsig) f_ty
              if p : P e' then
                have p' := .dot pe' (by simp; exact p)
                have e'_init := .dot pe'_init (by simp)
                return ⟨res.calls, res.strings, tau, e', p', e'_init⟩
              else throw <| fail e' p
            | none => throw <| Error.expr exp <|
              s!"Invalid field '{field}' for struct type '{Typ.mem (.struct name)}'"
          else throw <| fail (.deref obj) pe
        else throw <| Error.texpr res.texpr s!"Struct '{name}' is not defined"
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
      if p : P e' then
        have p' := .deref res.valid (by simp; exact p)
        have e'_init := .deref res.init (by simp)
        return ⟨res.calls, res.strings, tau, e', p', e'_init⟩
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
        if p : P e' then
          have p' := .index resa.valid resi.valid (by simp; exact p)
          have e'_init := .index resa.init resi.init (by simp)
          return ⟨calls, strings, tau, e', p', e'_init⟩
        else throw <| fail e' p
      else throw <| Error.expr exp <|
      s!"Array indices must be type '{Typ.prim .int}' not type '{resi.type}'"
    | _ => throw <| Error.expr exp <|
      s!"Array indexing must be on array types not type '{resa.type}'"

  | .result           =>
    match ctx.ret_type with
    | .some tau =>
      if p : P (τ := tau) .result then
        have p' := .result (by simp; exact p)
        have e'_init := .result (by simp [Tst.Initialised.expr])
        return ⟨ctx.calls, ctx.strings, tau, .result, p', e'_init⟩
      else throw <| fail .result p
    | .none     => throw <| Error.expr exp <|
      s!"Cannot use result when function's return type is void"

  | .length e         =>
    let res ← small_nonvoid <| expr ctx P fail e
    match eq : res.type with
    | .mem (.array tau) =>
      let e' := .length (res.texpr.arrType tau eq)
      if p : P e' then
        have p' := .length res.valid (by simp; exact p)
        have e'_init := .length res.init (by simp)
        return ⟨res.calls, res.strings, .prim .int, e', p', e'_init⟩
      else throw <| fail e' p
    | _ => throw <| Error.expr exp <|
      s!"Can only check the length of arrays not of type '{res.type}'"

def exprs (ctx : FuncCtx)
          (init_set : Tst.Initialised.Acc)
          (P : {τ : Typ} → Tst.Expr Δ Γ τ → Bool)
          (fail : {τ : Typ} → (te : Tst.Expr Δ Γ τ) → ¬P te → Error)
          (exps : List Ast.Expr)
          : Except Error (Result.List P init_set) := do
  match exps with
  | [] => return ⟨ctx.calls, ctx.strings, []⟩
  | e :: es =>
    let rese ← small_nonvoid <| expr ctx (init_set := init_set) P fail e
    let reses ← exprs ctx init_set P fail es
    let calls   := rese.calls.merge reses.calls
    let strings := rese.strings ∪ reses.strings
    let texprs  :=
      ⟨rese.type, rese.texpr, rese.valid, rese.init⟩ :: reses.texprs
    return ⟨calls, strings, texprs⟩
end

end Synth.Expr

namespace Synth.LValue

structure Result
    (Δ : Tst.GCtx) (Γ : Tst.FCtx) (init_set : Tst.Initialised.Acc)
where
  calls : Tst.Calls
  type : Typ
  lval : Tst.LValue Δ Γ type
  init : Tst.Initialised.LValue lval init_set

def small (res : Except Error (Result Δ Γ init_set))
    : Except Error (Result Δ Γ init_set) := do
  if (← res).type.isSmall
  then return (← res)
  else throw <| Error.msg s!"LValue has large type"

set_option maxHeartbeats 300000 in
def lvalue (ctx : FuncCtx) (lval : Ast.LValue)
    : Except Error (Result Δ Γ init_set) := do
  match lval with
  | .var var =>
    match h : Γ var with
    | some (.var tau) =>
      if is_init : init_set var then
        let lv' := .var var h
        have lv'_init := .var (by simp [Tst.Initialised.lval]; exact is_init)
        return ⟨ctx.calls, tau, lv', lv'_init⟩
      else throw <| Error.lval lval s!"Variable not initialised"
    | _ => throw <| Error.lval lval s!"Variable not declared"

  | .dot lv field =>
    let res ← lvalue ctx lv
    match tyeq : res.type with
    | .mem (.struct name) =>
      match hsig : Δ.struct name with
      | some status =>
        if defined : status.defined then
          match f_ty : status.fields field with
          | some tau =>
            let lv' :=
              .dot (res.lval.structType name tyeq) field
                (by rw [←defined]; exact hsig) f_ty
            have lv'_init := .dot res.init (by simp)
            return ⟨res.calls, tau, lv', lv'_init⟩
          | none => throw <| Error.lval lval <|
            s!"Invalid field '{field}' for struct type '{res.type}'"
        else throw <| Error.lval lval s!"Struct '{name}' is not defined"
      | none => throw <| Error.lval lval s!"Struct {name} is not defined"
    | _ => throw <| Error.lval lval <|
      s!"Field accessor expects a struct not type '{res.type}'"

  | .arrow lv field =>
    let res ← lvalue ctx lv
    match tyeq : res.type with
    | .mem (.pointer <| .mem (.struct name)) =>
      match hsig : Δ.struct name with
      | some status =>
        if defined : status.defined then
          match f_ty : status.fields field with
          | some tau =>
            let dref' : Tst.LValue Δ Γ _ :=
              .deref (res.lval.ptrType (.mem (.struct name)) tyeq)
            have dref'_init : Tst.Initialised.LValue dref' init_set :=
              .deref res.init (by simp)
            let lv' := .dot (dref'.structType name (by rfl)) field
              (by rw [←defined]; exact hsig) f_ty
            have lv'_init := .dot dref'_init (by simp)
            return ⟨res.calls, tau, lv', lv'_init⟩
          | none => throw <| Error.lval lval <|
            s!"Invalid field '{field}' for struct type '{res.type}'"
        else throw <| Error.lval lval s!"Struct '{name}' is not defined"
      | none => throw <| Error.lval lval s!"Struct '{name}' is not defined"
    | _ => throw <| Error.lval lval <|
      s!"Arrow operator expects a struct pointer not type '{res.type}'"
  | .deref lv =>
    let res ← lvalue ctx lv
    match tyeq : res.type with
    | .mem (.pointer tau)  =>
      have lv'_init := .deref res.init (by simp)
      return ⟨res.calls, tau, .deref (res.lval.ptrType tau tyeq), lv'_init⟩
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
      have lv'_init := .index resa.init (by simp; exact resi.init) (by simp)
      return ⟨calls, tau, lv', lv'_init⟩
    | .mem (.array _tau), _ => throw <| Error.lval lval <|
      s!"Array indices must be type '{Typ.prim .int}' not type '{resi.type}'"
    | _, _ => throw <| Error.lval lval <|
      s!"Array indexing must be on array types not type '{resa.type}'"

end Synth.LValue

namespace Synth.Anno

structure Result
    (Δ : Tst.GCtx) (Γ : Tst.FCtx)
    (P : Tst.Anno Δ Γ → Bool)
    (init_set : Tst.Initialised.Acc)
where
  anno : {a : Tst.Anno Δ Γ // P a}
  init : Tst.Initialised.Anno anno.val init_set

structure Result.List
    (Δ : Tst.GCtx) (Γ : Tst.FCtx)
    (P : Tst.Anno Δ Γ → Bool)
    (init_set : Tst.Initialised.Acc)
where
  ctx   : FuncCtx
  annos : List {a : Tst.Anno Δ Γ // P a}
  init  : Tst.Initialised.Anno.List (annos.map (·.val)) init_set

def func (ctx : FuncCtx) (as : List Ast.Anno)
    : Except Error (Result.List Δ Γ Tst.Anno.function init_set) := do
  match as with
  | []                  => return ⟨ctx, [], .nil⟩
  | .requires e :: rest =>
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr (init_set := init_set) ctx Tst.Expr.no_result Error.no_result e
    if tyeq : res.type = .prim .bool then
      let calls' := ctx.calls.merge (res.calls.mapVal (fun _ _ => true))
      let ⟨ctx', rest', rest'_init⟩ ←
        func {ctx with calls := calls'} (init_set := init_set) rest
      let e' := ⟨res.texpr.boolType tyeq, res.valid⟩
      let anno' := ⟨.requires e', by simp⟩
      have anno'_init := .requires (by simp; exact res.init)
      return ⟨ctx', anno' :: rest', .cons anno'_init rest'_init⟩
    else
      throw <| Error.expr e <|
        s!"Requires must have type {Typ.prim .bool} not type '{res.type}'"

  | .ensures  e :: rest =>
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx (fun _ => true) (fun _ np => by simp at np) e
    if tyeq : res.type = .prim .bool then
      let calls' := ctx.calls.merge (res.calls.mapVal (fun _ _ => true))
      let ⟨ctx', rest', rest'_init⟩ ← func {ctx with calls := calls'} rest
      let anno' := ⟨.ensures (res.texpr.boolType tyeq), by simp⟩
      have anno'_init := .ensures res.init
      return ⟨ctx', anno' :: rest', .cons anno'_init rest'_init⟩
    else
      throw <| Error.expr e <|
        s!"Ensures must have type {Typ.prim .bool} not type '{res.type}'"

  | .loop_invar _ :: _ =>
    throw <| Error.msg "Loop invariants can only precede loop bodies"
  | .assert _ :: _ =>
    throw <| Error.msg "Assert cannot annotate functions"

def loop (ctx : FuncCtx) (as : List Ast.Anno)
    : Except Error (Result.List Δ Γ Tst.Anno.loop init_set) := do
  match as with
  | []            => return ⟨ctx, [], .nil⟩
  | .requires _   :: _    => throw <| Error.msg "Requires can only annotate functions"
  | .ensures  _   :: _    => throw <| Error.msg "Ensures can only annotate functions"
  | .loop_invar e :: rest =>
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_result Error.no_result e
    if tyeq : res.type = .prim .bool then
      let calls' := ctx.calls.merge (res.calls.mapVal (fun _ _ => true))
      let ⟨ctx', rest', rest'_init⟩ ← loop {ctx with calls := calls'} rest
      let e' := ⟨res.texpr.boolType tyeq, res.valid⟩
      let anno' := ⟨.loop_invar e', by simp⟩
      have anno'_init := .loop_invar (by simp; exact res.init)
      return ⟨ctx', anno' :: rest', .cons anno'_init rest'_init⟩
    else
      throw <| Error.expr e <|
        s!"Loop invariants must have type {Typ.prim .bool} not type '{res.type}'"

  | .assert _ :: _       => throw <| Error.msg "Assert cannot annotate loops"

def free (ctx : FuncCtx) (a : Ast.Anno)
    : Except Error (FuncCtx × Result Δ Γ Tst.Anno.free init_set) := do
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
      let ctx' := {ctx with calls := calls'}
      let anno' := ⟨.assert ⟨res.texpr.boolType tyeq, res.valid⟩, by simp⟩
      have anno'_init := .assert res.init
      return ⟨ctx', anno', anno'_init⟩
    else
      throw <| Error.expr e <|
        s!"Assert must have type {Typ.prim .bool} not type '{res.type}'"

end Synth.Anno

namespace Stmt

structure Result
    (Δ : Tst.GCtx) (Γ : Tst.FCtx) (ρ : Option Typ)
    (init_set : Tst.Initialised.Acc)
    (rets : Bool)
where
  ctx       : FuncCtx
  stmt      : Tst.Stmt Δ Γ ρ
  init_set' : Tst.Initialised.Acc
  init      : Tst.Initialised.Stmt stmt init_set init_set'
  rets'     : Bool
  returns   : Tst.Returns.Stmt stmt rets rets'

structure Result.List
    (Δ : Tst.GCtx) (Γ : Tst.FCtx) (ρ : Option Typ)
    (init_set : Tst.Initialised.Acc)
    (rets : Bool)
where
  ctx   : FuncCtx
  stmts : Tst.Stmt.List Δ Γ ρ
  init_set' : Tst.Initialised.Acc
  init      : Tst.Initialised.Stmt.List stmts init_set init_set'
  rets'     : Bool
  returns   : Tst.Returns.Stmt.List stmts rets rets'

@[inline] private def wrapError
    (stmt : Ast.Stmt)
    (res : Except Error α)
    : Except Error α :=
  res.tryCatch (fun err => throw {err with statement := some stmt})

set_option maxHeartbeats 2000000 in -- can probs reduce this a bunch
mutual
def stmt
    {Δ : Tst.GCtx} {Γ : Tst.FCtx} {ρ : Option Typ}
    {init_set : Tst.Initialised.Acc}
    (ctx : FuncCtx) (rets : Bool) (stm : Ast.Stmt)
    : Except Error (Result Δ Γ ρ init_set rets) := do
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
          let Γ' := Γ.updateVar name tau -- false
          let name' : Typ.Typed Symbol := ⟨tau, name⟩
          let init_set_body :=
            Tst.Initialised.init (Δ := Δ) (Γ := Γ) init_set (.decl name')

          let res ← stmts (Γ := Γ') (init_set := init_set_body)
              {ctx' with calls := ctx.calls, strings := ctx.strings} rets body
          let symbols' := -- restore old symbol status
            match ctx.symbols.find? name with
            | some status => res.ctx.symbols.insert name status
            | none => res.ctx.symbols.erase name
          let oldCtx := { res.ctx with symbols := symbols' }

          let stmt' := .decl name' (by simp) res.stmts
          let init_set' :=
            Tst.Initialised.join init_set_body res.init_set' stmt'
          have stmt'_init := .decl (by simp) res.init (by simp)
          have stmt'_rets := .decl (by simp) res.returns (by simp)

          return ⟨oldCtx, stmt', init_set', stmt'_init, res.rets', stmt'_rets⟩

        | some e =>
          let res_init ← handle <| Synth.Expr.small_nonvoid <|
            Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
          -- types must be equivalent on both sides
          if ty_equiv : tau.equiv res_init.type then
            let e_init' := ⟨res_init.texpr, res_init.valid⟩

            -- if we are assigning something to struct type, must be defined
            if let Typ.mem (.struct sname) := res_init.type then
              match ctx.structs.find? sname with
              | some status =>
                if ¬ status.defined then throw <| Error.stmt stm <|
                  s!"Expression '{res_init.texpr}' has undefined type '{res_init.type}'"
              | _ => throw <| Error.stmt stm <|
                s!"Expression '{res_init.texpr}' has undefined/undeclared type '{res_init.type}'"

            let Γ' := Γ.updateVar name tau
            let name' := ⟨tau, name⟩
            let init_set_body :=
              Tst.Initialised.init init_set (.decl_init name' e_init')

            let calls := res_init.calls.merge ctx'.calls
            let strings := res_init.strings ∪ ctx'.strings

            let res ← stmts (Γ := Γ') (init_set := init_set_body)
              {ctx' with calls, strings} rets body
            let symbols' := -- restore old symbol status
              match ctx.symbols.find? name with
              | some status => res.ctx.symbols.insert name status
              | none => res.ctx.symbols.erase name
            let oldCtx := { res.ctx with symbols := symbols' }

            let stmt' :=
              .decl_init name' e_init' ty_equiv (by simp) res.stmts
            let init_set' :=
              Tst.Initialised.join init_set_body res.init_set' stmt'
            have stmt'_init :=
              .decl_init (a₂ := init_set)
                res_init.init (by simp) res.init (by simp)
            have stmt'_rets :=
              .decl_init (a₂ := rets) (a₃ := rets) (a₄ := res.rets')
                (by simp) (by simp) res.returns (by simp)

            return ⟨oldCtx, stmt', init_set', stmt'_init, res.rets', stmt'_rets⟩
          else throw <| Error.stmt stm <|
            s!"Variable '{name}' has mismatched types. Declaration expects '{tau}' but {res_init.texpr} has type '{res_init.type}'"

  | .assn lv op e =>
    match h : lv, op with
    | .var var, .eq =>
      match h : Γ var with
      | none => throwS s!"Variable '{var}' must be declared before assignment"
      | some (.var tau) =>
        let res ← handle <| Synth.Expr.small_nonvoid <|
            Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
        let ctx := {ctx with calls := res.calls, strings := res.strings}

        if ty_equiv : tau.equiv res.type then
          let Γ' := Γ.updateVar var tau
          let ctx' := ctx
            -- if /- initialised -/true then ctx else
              -- let symbols' :=
                -- ctx.symbols.insert var (.var ⟨tau, true⟩)
              -- { ctx with symbols := symbols' }

          let lv' := Tst.LValue.var (τ := tau) var (h)
          let e' : Tst.Expr.NoContract Δ Γ _ := ⟨res.texpr, res.valid⟩
          have is_var := by simp [lv']; rfl
          let stmt' := .assign_var lv' is_var e' (ty_equiv)
          let init_set' :=
            Tst.Initialised.init init_set (.assign_var lv' is_var e')
          have stmt'_init :=
            .assign_var (a₂ := init_set) (a₃ := init_set')
              res.init (by simp) (by simp)
          have stmt'_rets :=
            .assign_var (a₂ := rets) (a₃ := rets) (by simp) (by simp) (by simp)

          return ⟨ctx', stmt', init_set', stmt'_init, rets, stmt'_rets⟩
        else throwS s!"Assignment of '{var}' expects type '{tau}' but got '{res.type}'"
      | some (.func _)  => throwS s!"Cannot assign to function '{var}'"
      | some (.alias _) => throwS s!"Cannot assign to type alias '{var}'"
    | _ , _ =>
      let resl ← handleLV <| Synth.LValue.small <| Synth.LValue.lvalue ctx lv
      let resr ← handle <| Synth.Expr.small_nonvoid <|
        Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
      let ctx := { ctx with calls := resl.calls.merge resr.calls
                          , strings := resr.strings
                  }
      match op_eq : op with
      | .eq =>
        if ty_equiv : resl.type.equiv resr.type then
          have : ¬resl.lval.is_var := by sorry
          let e' := ⟨resr.texpr, resr.valid⟩

          let stmt' := .assign resl.lval this e' ty_equiv
          let init_set' :=
            Tst.Initialised.init init_set (.assign resl.lval this e')
          have stmt'_init := .assign resl.init (by simp) resr.init (by simp)
          have stmt'_rets :=
            .assign (a₂ := rets) (a₃ := rets) (a₄ := rets)
              (Tst.Returns.lval_fold rets resl.lval)
              (by simp) (by simp) (by simp)

          return ⟨ctx, stmt', init_set', stmt'_init, rets, stmt'_rets⟩
        else throwS s!"Left side of assignment has type '{resl.type}' doesn't match the right side '{resr.type}'"
      | .aseq binop =>
        if l_eq : resl.type = .prim .int then
          if r_eq : resr.type = .prim .int then
            let lv' := resl.lval.intType l_eq
            let e'  := ⟨resr.texpr.intType r_eq, resr.valid⟩
            let op' := Trans.int_binop binop

            let stmt' := .asnop lv' op' e'
            let init_set' :=
              Tst.Initialised.init init_set (.asnop resl.lval op' e')
            have stmt'_init := .asnop (by simp) resl.init resr.init (by simp)
            have stmt'_rets :=
              .asnop (a₂ := rets) (a₃ := rets) (a₄ := rets)
                (by simp) (Tst.Returns.lval_fold rets lv') (by simp) (by simp)

            return ⟨ctx, stmt', init_set', stmt'_init, rets, stmt'_rets⟩
          else throwS s!"Assignment with operations must have type '{Typ.prim .int}' but right side is '{resr.type}'"
        else throwS s!"Assignment with operations must have type '{Typ.prim .int}'  but left side is '{resl.type}'"

  | .ite cond tt ff =>
    let resc ← handle <| Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract cond
    let ctx' := {ctx with calls := resc.calls, strings := resc.strings}
    match c_eq : resc.type with
    | .prim .bool =>
      let rest ← stmts ctx' rets tt
      let resf ← stmts ctx' rets ff
      let cond' := ⟨resc.texpr.boolType c_eq, resc.valid⟩

      let stmt' := .ite cond' rest.stmts resf.stmts
      let init_set' := Tst.Initialised.init init_set (.ite cond')
      let init_set'' := Tst.Initialised.join rest.init_set' resf.init_set' stmt'
      have stmt'_init :=
        .ite (a₂ := init_set) (a₃ := init_set')
          resc.init (by simp) rest.init resf.init (by simp)
      let rets' := rest.rets' && resf.rets'
      have stmt'_rets :=
        .ite (a₂ := rets) (a₃ := rets) (a₄ := rets')
          (by simp) (by simp) rest.returns resf.returns (by simp)

      return ⟨rest.ctx.join resf.ctx, stmt', init_set'', stmt'_init, rets', stmt'_rets⟩
    | _ => throwS s!"If condition must be of type '{Typ.prim .bool}' not '{resc.type}'"

  | .while cond annos body =>
    let resc ← handle <| Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract cond
    let resa ← handleAnnos <| Synth.Anno.loop ctx annos
    match c_eq : resc.type with
    | .prim .bool =>
      let resb ← stmts resa.ctx rets body
      let cond' : Tst.Expr.NoContract _ _ _ :=
        ⟨resc.texpr.boolType c_eq, resc.valid⟩
      let ctx'' :=
        { ctx with calls   := resb.ctx.calls.merge resc.calls
                 , strings := resb.ctx.strings ∪ resc.strings
        }

      let stmt' := Tst.Stmt.while cond' resa.annos resb.stmts
      let init_set' := Tst.Initialised.init init_set (.while cond')
      let init_set'' := Tst.Initialised.join init_set resb.init_set' stmt'
      have stmt'_init :=
        Tst.Stmt.Fold.while (P := Tst.Initialised.Predicate) (cond := cond')
          (a₂ := init_set) (a₃ := init_set) (a₄ := init_set')
          resc.init resa.init (by simp) resb.init (by simp)
      have stmt'_rets :=
        Tst.Stmt.Fold.while (P := Tst.Returns.Predicate) (cond := cond')
          (a₂ := rets) (a₃ := rets) (a₄ := rets) (a₆ := rets)
          (by simp) (by simp) (by simp) resb.returns (by simp)

      return ⟨ctx'', stmt', init_set'', stmt'_init, rets, stmt'_rets⟩
    | _ => throwS s!"Loop condition must be of type '{Typ.prim .bool}' not '{resc.type}'"

  | .return .none =>
    match is_void : ρ with
    | some _ => throw <| Error.stmt stm <|
        s!"Expected return type is '{ctx.ret_type}'" -- todo change this msg?
    | none =>
      let ctx' := {ctx with returns := true}
      let stmt' := .return_void (by simp)
      let init_set' := Tst.Initialised.stmt init_set stmt'
      have stmt'_init := .return_void (by simp)
      have stmt'_rets := .return_void (by simp)
      return ⟨ctx', stmt', init_set', stmt'_init, true, stmt'_rets⟩

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

        let stmt' := .return_tau e'
        let init_set' := Tst.Initialised.stmt init_set stmt'
        have stmt'_init :=
          .return_tau (a₂ := init_set) (by simp) res.init (by simp)
        have stmt'_rets :=
          .return_tau (a₂ := rets) (a₃ := rets) (by simp) (by simp) (by simp)

        return ⟨ctx', stmt', init_set', stmt'_init, true, stmt'_rets⟩
      else throw <| Error.stmt stm <|
        s!"Expected return type was '{ctx.ret_type}' but got '{res.type}'"

  | .assert e =>
    let res ← handle <| Synth.Expr.small_nonvoid (init_set := init_set) <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
    match tyeq : res.type with
    | .prim .bool =>
      let e'   := ⟨res.texpr.boolType tyeq, res.valid⟩
      let ctx' := { ctx with calls := res.calls, strings := res.strings }

      let stmt' := .assert e'
      let init_set' := Tst.Initialised.stmt init_set stmt'
      have stmt'_init :=
        .assert (a₂ := init_set) (by simp) (by exact res.init) (by simp)
      have stmt'_rets :=
        .assert (a₂ := rets) (a₃ := rets) (a₄ := rets)
          (by simp) (by simp) (by simp)

      return ⟨ctx', stmt', init_set', stmt'_init, rets, stmt'_rets⟩
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

      let stmt' := .error e'
      let init_set' := Tst.Initialised.stmt init_set stmt'
      have stmt'_init :=
        .error (a₂ := init_set) (by simp) (by exact res.init) (by simp)
      have stmt'_rets :=
        .error (a₂ := rets) (a₃ := rets) (by simp) (by simp) (by simp)

      return ⟨ctx', stmt', init_set', stmt'_init, true, stmt'_rets⟩
    | _ => throwS s!"Error condition must be of type '{Typ.prim .string}' not '{res.type}'"

  | .exp e =>
    let res ← handle <| Synth.Expr.small <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract e
    let e'   := ⟨res.texpr, res.valid⟩
    let ctx' := {ctx with calls := res.calls, strings := res.strings}

    let stmt' := .expr e'
    let init_set' := Tst.Initialised.stmt init_set stmt'
    have stmt'_init :=
      .expr (a₂ := init_set) (by simp) (by exact res.init) (by simp)
    have stmt'_rets :=
      .expr (a₂ := rets) (a₃ := rets) (by simp) (by simp) (by simp)

    return ⟨ctx', stmt', init_set', stmt'_init, rets, stmt'_rets⟩

  | .anno a =>
    let (ctx', res) ← handleAnno <| Synth.Anno.free (init_set := init_set) ctx a

    let stmt' := Tst.Stmt.anno res.anno
    let init_set' := Tst.Initialised.stmt init_set stmt'
    have stmt'_init :=
      Tst.Stmt.Fold.anno (a₂ := init_set)
        (by simp) (by exact res.init) (by simp)
    have stmt'_rets :=
      .anno (a₂ := rets) (a₃ := rets) (by simp) (by simp) (by simp)

    return ⟨ctx', stmt', init_set', stmt'_init, rets, stmt'_rets⟩


def stmts (ctx : FuncCtx)
          (rets : Bool)
          (body : List Ast.Stmt)
          : Except Error (Result.List Δ Γ ρ init_set rets) := do
  match body with
  | [] => return ⟨ctx, .nil, init_set, .nil, false, sorry⟩
  | b::bs =>
    let resb ← stmt ctx rets b
    /- We need to typecheck after returns but we disregard the result.
       TOOD: think about how this could be structurally enforced.
     -/
    if resb.rets' then
      let resbs : (Result.List Δ Γ ρ _ _) ←
        stmts (init_set := resb.init_set') resb.ctx resb.rets' bs
      let stmts' := .cons resb.stmt .nil
      have stmts'_init := .cons resb.init .nil
      have stmts'_rets := .cons resb.returns .nil
      let ctx := resbs.ctx -- use later context bc we care about string/calls
      return ⟨ctx, stmts', resb.init_set', stmts'_init, resb.rets', stmts'_rets⟩
    else
      let resbs ← stmts (init_set := resb.init_set') resb.ctx resb.rets' bs
      let stmts' := .cons resb.stmt resbs.stmts
      have stmts'_init := .cons resb.init resbs.init
      have stmts'_rets := .cons resb.returns resbs.returns
      let ctx := resbs.ctx
      return ⟨ctx, stmts', resbs.init_set', stmts'_init, resbs.rets', stmts'_rets⟩
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
  if extern && Symbol.main == f.name then
    throw <| Error.func f.name s!"Function 'main' cannot appear in headers"
  else
    let (ctx', fctx, ret) ← func ctx extern false f.name f.type f.params
    let params ← Trans.params fctx f.params
    let init_Γ := Tst.FCtx.init Δ params
    let init_set := Tst.Initialised.Acc.ofList (params.map (·.data))
    let res ← Synth.Anno.func (Γ := init_Γ) (init_set := init_set) fctx f.annos
    let fdecl := Tst.GDecl.fdecl
      { ret
      , name := f.name
      , params
      , annos := res.annos
      , initial_init := init_set
      , annos_init   := res.init
      }
    return ⟨{ctx' with calls := ctx'.calls.merge res.ctx.calls}, _, some fdecl⟩

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
    let init_set := Tst.Initialised.Acc.ofList (params.map (·.data))
    let resa ← Synth.Anno.func (Γ := init_Γ) (init_set := init_set) fctx f.annos
    let fdecl : Tst.FDecl Δ :=
      { ret
      , name := f.name
      , params
      , init_Γ
      , annos := resa.annos
      , initial_init := init_set
      , annos_init   := resa.init
      }

    let Γ := init_Γ.addFunc f.name retTy params
    let res : Stmt.Result.List Δ _ ret _ _ ←
      Stmt.stmts (Δ := Δ) (Γ := Γ) (ρ := ret)
        (init_set := init_set) resa.ctx false f.body
        |>.tryCatch (fun err => throw {err with function := some f.name})

    if rets_valid : ¬(ret.isNone || res.rets') then
      throw <| Error.func f.name s!"Function does not return on some paths"
    else

    let funcCalls := ctx'.funcCalls.insert f.name res.ctx.calls
    let calls     := ctx'.calls.merge res.ctx.calls
    let strings   := ctx'.strings ∪ res.ctx.strings

    let body'' :=
      if ret_none : ret.isNone then
        res.stmts.consEnd (Tst.Stmt.return_void ret_none)
      else res.stmts

    let fdef := Tst.GDecl.fdef
      { toFDecl := fdecl
      , body := body''
      , post_init :=
          if ret_none : ret.isNone then
            Tst.Initialised.stmt res.init_set'
              (Tst.Stmt.return_void (Δ := Δ) (Γ := Γ) ret_none)
          else res.init_set'
      , body_init := by
          if ret_none : ret.isNone then
            simp [body'', ret_none]
            exact Tst.Stmt.List.Fold.consEnd (a₂ := res.init_set')
                    res.stmts res.init (.return_void (by simp))
          else simp [body'', ret_none]; exact res.init
      , body_rets := by
          if ret_none : ret.isNone then
            simp [body'', ret_none]
            exact Tst.Stmt.List.Fold.consEnd (a₂ := res.rets') (a₃ := true)
                    res.stmts res.returns (.return_void (by simp))
          else
            have := res.returns
            simp [ret_none] at rets_valid
            simp [body'', ret_none]
            rw [rets_valid] at this
            exact this
      }
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
