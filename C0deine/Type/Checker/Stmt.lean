/- C0deine - Type.Checker.Stmt
   Typechecking statements
   - Thea Brick
 -/
import C0deine.Type.Checker.LValue
import C0deine.Type.Checker.Anno

namespace C0deine.Typechecker.Stmt

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
