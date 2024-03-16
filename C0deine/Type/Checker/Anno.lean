/- C0deine - Type.Checker.Anno
   Typechecking annotations
   - Thea Brick
 -/
import C0deine.Type.Checker.Expr

namespace C0deine.Typechecker.Synth.Anno

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
    let anno_ctx := {ctx with calls := Symbol.Map.empty}
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr anno_ctx Tst.Expr.no_result Error.no_result e
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
    let anno_ctx := {ctx with calls := Symbol.Map.empty}
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr anno_ctx (fun _ => true) (fun _ np => by simp at np) e
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
    let anno_ctx := {ctx with calls := Symbol.Map.empty}
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr anno_ctx Tst.Expr.no_result Error.no_result e
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
    let anno_ctx := {ctx with calls := Symbol.Map.empty}
    let res ← Synth.Expr.small_nonvoid <|
      Synth.Expr.expr anno_ctx Tst.Expr.no_result Error.no_result e
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
