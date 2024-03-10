/- C0deine - TST.Context
   Utilies for implementing the TST, specifically different contexts.
   - Thea Brick
 -/
import Numbers
import C0deine.AuxDefs
import C0deine.Type.Typ
import C0deine.Context.Symbol
import C0deine.Utils.Comparison

namespace C0deine.Tst

open Typ

structure FuncSig where
  arity  : Nat
  argTys : Fin arity → Typ
  retTy  : Typ    -- use .any if void

structure Status.Func where
  type    : FuncSig
  defined : Bool

structure Status.Struct where
  fields  : Symbol → Option Typ
  defined : Bool

inductive Status.Symbol
| var   (v : Typ)
| func  (f : Status.Func)
| alias (t : Typ)

-- use Status.Symbol to prevent collisions with funcs/tydefs
structure FCtx where
  syms : Symbol → Option Status.Symbol
  ret  : Option Typ

@[inline] def FCtx.update (Γ : FCtx) (x : Symbol) (s : Status.Symbol) : FCtx :=
  { Γ with syms := Function.update Γ.syms x (some s) }
@[inline] def FCtx.updateVar (Γ : FCtx) (x : Symbol) (τ : Typ) : FCtx :=
  Γ.update x (.var τ)
@[inline] def FCtx.updateFunc
    (Γ : FCtx) (x : Symbol) (s : Status.Func) : FCtx :=
  Γ.update x (.func s)
@[inline] def FCtx.ofParams
    (ret : Option Typ) (params : List (Typed Symbol)) : FCtx :=
  ⟨(params.map (fun p => (p.data, .var p.type))).toMap, ret⟩
@[inline] def FCtx.addFunc
    (Γ : FCtx) (f : Symbol) (retTy : Typ) (params : List (Typed Symbol))
    : FCtx :=
  let params_Γ := FCtx.ofParams retTy params
  let args := fun i => params.get i |>.type
  let status := ⟨⟨params.length, args, retTy⟩, true⟩
  ⟨ fun x => -- re-add params bc they shadow the function definition
      match params_Γ.syms x with
      | some status => some status
      | none => if x = f then some (.func status) else Γ.syms x
  , retTy
  ⟩

structure GCtx where
  symbols : Symbol → Option Status.Symbol := fun _ => none
  struct  : Symbol → Option Status.Struct := fun _ => none
deriving Inhabited

@[inline] def FCtx.init
    (Δ : GCtx) (ret : Option Typ) (params : List (Typed Symbol)) : FCtx :=
  let params_Γ := FCtx.ofParams ret params
  ⟨ fun x =>
      match params_Γ.syms x with
      | some status => some status
      | none => Δ.symbols x
  , ret
  ⟩
