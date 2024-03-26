/- C0deine - Type.Checker.LValue
   Typechecking lvalues
   - Thea Brick
 -/
import C0deine.Type.Checker.Expr

namespace C0deine.Typechecker.Synth.LValue

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

def lvalue (ctx : FuncCtx) (lval : Ast.LValue)
    : Except Error (Result Δ Γ init_set) := do
  match lval with
  | .var var =>
    match h : Γ.syms var with
    | some (.var tau) =>
      if is_init : init_set var then
        let lv' := .var var h
        have lv'_init :=
          .var (by simp only [ Tst.Stmt.Predicate.toLValuePred
                             , Tst.Initialised.Predicate
                             , Tst.Initialised.lval
                             , is_init
                             , ↓reduceIte
                             ])
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
              .dot tyeq res.lval field (by rw [←defined]; exact hsig) f_ty
            have lv'_init :=
              .dot res.init
                (by simp only [ Tst.Stmt.Predicate.toLValuePred
                              , Tst.Initialised.Predicate
                              , Tst.Initialised.lval
                              ])
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
            let dref' : Tst.LValue Δ Γ _ := .deref tyeq res.lval
            have dref'_init : Tst.Initialised.LValue dref' init_set :=
              .deref res.init
                (by simp only [ Tst.Stmt.Predicate.toLValuePred
                              , Tst.Initialised.Predicate
                              , Tst.Initialised.lval
                              ])
            let lv' :=
              .dot (by rfl) dref' field (by rw [←defined]; exact hsig) f_ty
            have lv'_init :=
              .dot dref'_init
                (by simp only [ Tst.Stmt.Predicate.toLValuePred
                              , Tst.Initialised.Predicate
                              , Tst.Initialised.lval
                              ])
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
      have lv'_init :=
        .deref res.init
          (by simp only [ Tst.Stmt.Predicate.toLValuePred
                        , Tst.Initialised.Predicate
                        , Tst.Initialised.lval
                        ])
      return ⟨res.calls, tau, .deref tyeq res.lval, lv'_init⟩
    | _ => throw <| Error.lval lval <|
      s!"Cannot dereference a non-pointer type '{res.type}'"

  | .index arr indx =>
    let resa ← lvalue ctx arr
    let resi ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr ctx Tst.Expr.no_contract Error.no_contract indx
    let calls := resa.calls.merge resi.calls
    match tya_eq : resa.type, tyi_eq : resi.type with
    | .mem (.array tau), .prim .int =>
      let indx' := ⟨resi.texpr, resi.valid⟩
      let lv' := .index tya_eq tyi_eq resa.lval indx'
      have lv'_init :=
        .index resa.init
          (by simp only [ Tst.Stmt.Predicate.toLValuePred
                        , Tst.Initialised.Predicate
                        ]
              exact resi.init)
          (by simp only [ Tst.Stmt.Predicate.toLValuePred
                        , Tst.Initialised.Predicate
                        , Tst.Initialised.lval
                        ])
      return ⟨calls, tau, lv', lv'_init⟩
    | .mem (.array _tau), _ => throw <| Error.lval lval <|
      s!"Array indices must be type '{Typ.prim .int}' not type '{resi.type}'"
    | _, _ => throw <| Error.lval lval <|
      s!"Array indexing must be on array types not type '{resa.type}'"

end Synth.LValue
