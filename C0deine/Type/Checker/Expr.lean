/- C0deine - Type.Checker.Expr
   Typechecking expressions
   - Thea Brick
 -/
import C0deine.Type.Checker.Context
import C0deine.Type.Checker.Validation

namespace C0deine.Typechecker.Synth.Expr

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
  strings : _root_.List String
  texprs  : _root_.List (Result.Core P init_set)


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
    let e' := .num (by rfl) n
    if p : P e' then
      have p' := .num (by simp only [p, e', ↓reduceIte])
      have e'_init := .num (by dsimp only [Tst.Initialised.expr])
      return ⟨ctx.calls, ctx.strings, .prim .int, e', p', e'_init⟩
    else throw <| fail e' p

  | .char c            =>
    let e' := .char (by rfl) c
    if p : P e' then
      have p' := .char (by simp only [p, e', ↓reduceIte])
      have e'_init := .char (by dsimp only [Tst.Initialised.expr])
      return ⟨ctx.calls, ctx.strings, .prim .char, e', p', e'_init⟩
    else throw <| fail e' p

  | .str s             =>
    let strings' := if s ∉ ctx.strings then s::ctx.strings else ctx.strings
    let e' := .str (by rfl) s
    if p : P e' then
      have p' := .str (by simp only [p, e', ↓reduceIte])
      have e'_init := .str (by dsimp only [Tst.Initialised.expr])
      return ⟨ctx.calls, strings', .prim .string, e', p', e'_init⟩
    else throw <| fail e' p

  | .true              =>
    let e' := .true (by rfl)
    if p : P e' then
      have p' := .true (by simp only [p, e', ↓reduceIte])
      have e'_init := .true (by dsimp only [Tst.Initialised.expr])
      return ⟨ctx.calls, ctx.strings, .prim .bool, e', p', e'_init⟩
    else throw <| fail e' p

  | .false             =>
    let e' := .false (by rfl)
    if p : P e' then
      have p' := .false (by simp only [p, e', ↓reduceIte])
      have e'_init := .false (by dsimp only [Tst.Initialised.expr])
      return ⟨ctx.calls, ctx.strings, .prim .bool, e', p', e'_init⟩
    else throw <| fail e' p

  | .null              =>
    let e' := .null (by rfl)
    if p : P e' then
      have p' := .null (by simp only [p, e', ↓reduceIte])
      have e'_init := .null (by dsimp only [Tst.Initialised.expr])
      return ⟨ctx.calls, ctx.strings, .mem (.pointer .any), e', p', e'_init⟩
    else throw <| fail e' p

  | .unop op e         =>
    let res ← small_nonvoid <| expr ctx P fail e
    match op with
    | .int op =>
      let op' := match op with | .neg => Tst.UnOp.Int.neg | .not => .not
      if eq : res.type.equiv (.prim .int) then
        let e' := Tst.Expr.unop_int eq (by rfl) op' res.texpr
        if p : P e' then
          have p' := .unop_int res.valid (by simp only [p, e', ↓reduceIte])
          have e'_init := .unop_int res.init (by dsimp only [Tst.Initialised.expr])
          return ⟨res.calls, res.strings, .prim .int, e', p', e'_init⟩
        else throw <| fail e' p
      else throw <| Error.expr exp <|
        s!"Unary operator '{Tst.UnOp.int op'}' expects type '{Typ.prim .int}' but got '{res.type}'"
    | .bool .neg =>
      if eq : res.type.equiv (.prim .bool) then
        let e' := Tst.Expr.unop_bool eq (by rfl) (.neg) res.texpr
        if p : P e' then
          have p' := .unop_bool res.valid (by simp only [p, e', ↓reduceIte])
          have e'_init := .unop_bool res.init (by dsimp only [Tst.Initialised.expr])
          return ⟨res.calls, res.strings, .prim .bool, e', p', e'_init⟩
        else throw <| fail e' p
      else throw <| Error.expr exp <|
        s!"Unary operator '{Tst.UnOp.bool .neg}' expects type '{Typ.prim .bool}' but got '{res.type}'"

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
          let e' := .binop_int leq req (by rfl) op' resl.texpr resr.texpr
          if p : P e' then
            let lvalid : Tst.Expr.All _ resl.texpr := resl.valid
            let rvalid : Tst.Expr.All _ resr.texpr := resr.valid
            let p' := .binop_int lvalid rvalid (by simp only [p, e', ↓reduceIte])
            have e'_init :=
              .binop_int resl.init resr.init
                (by dsimp only [Tst.Initialised.expr])
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
            let e' :=
              .binop_eq (by rfl) cop is_equality resl.texpr resr.texpr eq eqtype
            if p : P e' then
              let lvalid : Tst.Expr.All _ resl.texpr := resl.valid
              let rvalid : Tst.Expr.All _ resr.texpr := resr.valid
              let p' := .binop_eq lvalid rvalid (by simp only [p, e', ↓reduceIte])
              have e'_init :=
                .binop_eq resl.init resr.init
                  (by dsimp only [Tst.Initialised.expr])
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
            let e' := .binop_rel_int leq req (by rfl) cop is_equality
                        resl.texpr resr.texpr
            if p : P e' then
              let p' :=
                .binop_rel_int resl.valid resr.valid
                  (by simp only [p, e', ↓reduceIte])
              have e'_init :=
                .binop_rel_int resl.init resr.init
                  (by dsimp only [Tst.Initialised.expr])
              return ⟨calls, strings, .prim .bool, e', p', e'_init⟩
            else throw <| fail e' p
          else
            if leq : resl.type = .prim .char then
              have req := by rw [eq] at leq; exact leq
              let e' := .binop_rel_char leq req (by rfl) cop is_equality
                          resl.texpr resr.texpr
              if p : P e' then
                let p' :=
                  .binop_rel_char resl.valid resr.valid
                    (by simp only [p, e', ↓reduceIte])
                have e'_init :=
                  .binop_rel_char resl.init resr.init
                    (by dsimp only [Tst.Initialised.expr])
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
          let e' := .binop_bool leq req (by rfl) op' resl.texpr resr.texpr
          if p : P e' then
            let p' :=
              .binop_bool resl.valid resr.valid (by simp only [p, e', ↓reduceIte])
            have e'_init :=
              .binop_bool resl.init resr.init
                (by dsimp only [Tst.Initialised.expr])
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
        let τ' := rest.type.intersect resf.type
        let e' := .ternop cbool (by rfl) resc.texpr rest.texpr resf.texpr eq
        if p : P e' then
          have p' :=
            .ternop resc.valid rest.valid resf.valid
              (by simp only [p, e', ↓reduceIte])
          have e'_init :=
            .ternop resc.init rest.init resf.init
              (by dsimp only [Tst.Initialised.expr])
          return ⟨calls, strings, τ', e', p', e'_init⟩
        else throw <| fail e' p
      else throw <| Error.expr exp <|
        s!"Ternary true branch has type '{rest.type}' but the false branch has type '{resf.type}'"
    else throw <| Error.expr exp s!"Ternary condition {resc.texpr} must be a bool"

  | .app f args        =>
    match is_func : Γ.syms f with
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
            let p' := .app valid (by simp only [p, e', ↓reduceIte])
            have e'_init := .app init (by dsimp only [Tst.Initialised.expr])
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
        have p' := .alloc (by simp only [p, e', ↓reduceIte])
        have e'_init := .alloc (by dsimp only [Tst.Initialised.expr])
        return ⟨ctx.calls, ctx.strings, .mem (.pointer tau'), e', p', e'_init⟩
      else throw <| fail e' p

  | .alloc_array tau e =>
    let res ← small_nonvoid <| expr ctx P fail e
    let opt_tau' := Trans.type ctx tau |>.filter (Trans.isSized ctx)
    match opt_tau' with
    | none      => throw <| Error.expr exp s!"Invalid array type"
    | some tau' =>
      if eq : res.type = .prim .int then
        let e' := .alloc_array eq tau' res.texpr
        if p : P e' then
          let p' := .alloc_array res.valid (by simp only [p, e', ↓reduceIte])
          have e'_init :=
            .alloc_array res.init (by dsimp only [Tst.Initialised.expr])
          return ⟨ctx.calls, ctx.strings, .mem (.array tau'), e', p', e'_init⟩
        else throw <| fail e' p
        else throw <| Error.expr exp <|
          s!"Array length expected an '{Typ.prim .int}' but got '{res.type}'"

  | .var name          =>
    match h : Γ.syms name with
    | some (.var tau) =>
      match is_init : init_set name with
      | true =>
          let e' := .var name h
          if p : P e' then
            have p' := .var (by simp only [p, e', ↓reduceIte])
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
              .dot eq res.texpr field (by rw [←defined]; exact hsig) f_ty
            if p : P e' then
              have p' := .dot res.valid (by simp only [p, e', ↓reduceIte])
              have e'_init :=
                .dot res.init (by dsimp only [Tst.Initialised.expr])
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
          let te' := Tst.Expr.deref eq res.texpr         -- todo better names
          if pe : P te' then
            have pe' : Tst.Expr.All P te' := by
              simp only [te']
              exact .deref res.valid (by simp only [pe, te', ↓reduceIte])
            have pe'_init : Tst.Initialised.Expr te' init_set := by
              simp only [Tst.Initialised.Expr]
              exact .deref res.init (by dsimp only [Tst.Initialised.expr])

            match f_ty : status.fields field with
            | some tau =>
              let e' :=
                .dot (by rfl) te' field (by rw [←defined]; exact hsig) f_ty
              if p : P e' then
                have p' := .dot pe' (by simp only [p, e', ↓reduceIte])
                have e'_init :=
                  .dot pe'_init (by dsimp only [Tst.Initialised.expr])
                return ⟨res.calls, res.strings, tau, e', p', e'_init⟩
              else throw <| fail e' p
            | none => throw <| Error.expr exp <|
              s!"Invalid field '{field}' for struct type '{Typ.mem (.struct name)}'"
          else throw <| fail te' pe
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
      let e' := .deref eq res.texpr
      if p : P e' then
        have p' := .deref res.valid (by simp only [p, e', ↓reduceIte])
        have e'_init := .deref res.init (by dsimp only [Tst.Initialised.expr])
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
        let e' := .index aeq ieq resa.texpr resi.texpr
        if p : P e' then
          have p' := .index resa.valid resi.valid (by simp only [p, e', ↓reduceIte])
          have e'_init :=
            .index resa.init resi.init (by dsimp only [Tst.Initialised.expr])
          return ⟨calls, strings, tau, e', p', e'_init⟩
        else throw <| fail e' p
      else throw <| Error.expr exp <|
      s!"Array indices must be type '{Typ.prim .int}' not type '{resi.type}'"
    | _ => throw <| Error.expr exp <|
      s!"Array indexing must be on array types not type '{resa.type}'"

  | .result           =>
    match h : Γ.ret with
    | .some tau =>
      if p : P (τ := tau) (.result h) then
        have p' := .result (by simp only [p, ↓reduceIte])
        have e'_init := .result (by dsimp only [Tst.Initialised.expr])
        return ⟨ctx.calls, ctx.strings, tau, .result h, p', e'_init⟩
      else throw <| fail (.result h) p
    | .none     => throw <| Error.expr exp <|
      s!"Cannot use result when function's return type is void"

  | .length e         =>
    let res ← small_nonvoid <| expr ctx P fail e
    match eq : res.type with
    | .mem (.array tau) =>
      let e' := .length eq res.texpr
      if p : P e' then
        have p' := .length res.valid (by simp only [p, e', ↓reduceIte])
        have e'_init := .length res.init (by dsimp only [Tst.Initialised.expr])
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
