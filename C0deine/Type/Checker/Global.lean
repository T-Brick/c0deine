/- C0deine - Type.Checker.Stmt
   Typechecking global declarations/definitions
   - Thea Brick
 -/
import C0deine.Type.Checker.Stmt

namespace C0deine.Typechecker.Global

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
    match ctx.symbols.get? name with
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
    let init_Γ := Tst.FCtx.init Δ ret params
    let init_set := Tst.Initialised.Acc.ofList (params.map (·.data))
    let res ← Synth.Anno.func (Γ := init_Γ) (init_set := init_set) fctx f.annos
    let fdecl := Tst.GDecl.fdecl {
        ret
        name := f.name
        params
        annos := res.annos
        initial_init := init_set
        annos_init   := res.init
        init_Γ := init_Γ
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
    let init_Γ := Tst.FCtx.init Δ ret params
    let init_set := Tst.Initialised.Acc.ofList (params.map (·.data))
    let resa ← Synth.Anno.func (Γ := init_Γ) (init_set := init_set) fctx f.annos
    let fdecl : Tst.FDecl Δ := {
        ret
        name := f.name
        params
        init_Γ
        annos := resa.annos
        initial_init := init_set
        annos_init   := resa.init
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
            simp only [ body''
                      , Tst.Initialised.Stmt.List
                      , Tst.Initialised.Predicate
                      , ret_none
                      ]
            exact Tst.Stmt.List.Fold.consEnd (a₂ := res.init_set')
                    res.stmts
                    res.init
                    (.return_void (by rfl))
          else
            simp only [ body''
                      , Tst.Initialised.Stmt.List
                      , Tst.Initialised.Predicate
                      , ret_none
                      ]
            exact res.init
      , body_rets := by
          if ret_none : ret.isNone then
            simp only [ body''
                      , Tst.Returns.Stmt.List
                      , Tst.Returns.Predicate
                      , ret_none
                      ]
            exact Tst.Stmt.List.Fold.consEnd (a₂ := res.rets') (a₃ := true)
                    res.stmts res.returns (.return_void (by rfl))
          else
            have := res.returns
            simp only [ ret_none
                      , Bool.false_or
                      , Bool.not_eq_true
                      , Bool.not_eq_false
                      ] at rets_valid
            simp only [ body''
                      , Tst.Returns.Stmt.List
                      , Tst.Returns.Predicate
                      , ret_none
                      ]
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
    match ctx.structs.get? s.name with
    | none =>
      ctx.structs.insert s.name ⟨Std.HashMap.emptyWithCapacity, false⟩
    | some _ => ctx.structs
  return ⟨{ctx with structs := structs'}, Δ, none⟩

def sdef (ctx : GlobalCtx) (s : Ast.SDef) : Except Error (Result Δ) := do
  let () ←
    match ctx.structs.get? s.name with
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
