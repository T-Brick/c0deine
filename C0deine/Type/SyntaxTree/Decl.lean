/- C0deine - TST.Decl
   Typed gloal declarations.
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Stmt

namespace C0deine.Tst

open Typ

structure SDef where
  name : Symbol
  fields : List (Typed Symbol)

structure FDecl (Δ : GCtx) where
  ret    : Option Typ
  name   : Symbol
  params : List (Typed Symbol)
  init_Γ : FCtx
  annos  : List (Anno.Function Δ init_Γ)
  initial_init : Initialised.Acc := Initialised.Acc.ofList (params.map (·.data))
  annos_init   : Initialised.Anno.List (annos.map (·.val)) initial_init

structure FDef (Δ : GCtx) extends FDecl Δ where
  body : Stmt.List Δ (init_Γ.addFunc name (Typ.flattenOpt ret) params) ret
  post_init : Initialised.Acc
  body_init : Initialised.Stmt.List body initial_init post_init
  body_rets : Returns.Stmt.List body false true

def GCtx.updateStruct (Δ : GCtx) (s : SDef) : GCtx :=
  let sig := ⟨Typed.toMap s.fields, true⟩
  { Δ with struct := Function.update Δ.struct s.name (some sig) }

def GCtx.updateFunc (Δ : GCtx) (f : FDecl Δ) (defined : Bool) : GCtx :=
  let arity  := f.params.length
  let argTys := fun i => (f.params.get i).type
  let retTy := match f.ret with | none => .any | some τ => τ

  let defined' := -- can declare a function after defining it
    if let some (.func status) := Δ.symbols f.name then
      defined || status.defined
    else defined

  let sig : Status.Func := ⟨⟨arity, argTys, retTy⟩, defined'⟩
  { Δ with symbols := FCtx.updateFunc Δ.symbols f.name sig}

inductive GDecl (Δ : GCtx) : GCtx → Type
| fdecl : (f : FDecl Δ) → GDecl Δ (Δ.updateFunc f false)
| fdef  : (f : FDef Δ)  → GDecl Δ (Δ.updateFunc f.toFDecl true)
| sdef  : (s : SDef)    → GDecl Δ (Δ.updateStruct s)

inductive GDecl.List : GCtx → GCtx → Type
| nil    : GDecl.List Δ Δ
| cons   : GDecl.List Δ₁ Δ₂ → (g : GDecl Δ₂ Δ₃) → GDecl.List Δ₁ Δ₃
| update : GDecl.List Δ₁ Δ₂ → GDecl.List Δ₁ Δ₃

/- Functions calls that a program makes
    True means the call is used in a contract, so the function must be pure.
-/
def Calls := Symbol.Map Bool

def Calls.merge (calls1 calls2 : Calls) : Calls :=
  calls1.mergeWith (fun _ x y => x || y) calls2


structure Prog where
  header_ctx : GCtx
  header     : GDecl.List {} header_ctx
  body_ctx   : GCtx
  body       : GDecl.List header_ctx body_ctx
  calls      : Calls
  strings    : List String


instance : ToString SDef where
  toString s :=
    s!"struct {s.name}".append ("{".append ( s!"{s.fields}".append "};"))

instance : ToString (FDecl Δ) where toString f :=
  s!"{f.ret} {f.name}({f.params})\n  {toString f.annos}"
instance : ToString (FDef Δ) where
  toString f :=
    let str_anno := toString f.annos
    let str_body := (toString f.body).replace "\n" "\n  "
    s!"{f.ret} {f.name}({f.params})\n  {str_anno}{str_body}\nend {f.name}"

def GDecl.toString : (GDecl Δ Δ') → String
  | .fdecl f => s!"{f}"
  | .fdef  f => s!"{f}"
  | .sdef  s => s!"{s}"
instance : ToString (GDecl Δ Δ') where toString := GDecl.toString

def GDecl.List.toStrings : GDecl.List Δ Δ' → _root_.List String
  | .nil => []
  | .cons gs g => g.toString :: gs.toStrings
  | .update gs => gs.toStrings

instance : ToString Prog where
  toString prog :=
    let calls_str  := prog.calls.toList.map (fun (f, pure) =>
        if pure then s!"{f} (pure)" else s!"{f}")
      |> String.intercalate "\n  "
    let string_str := prog.strings.map (·.sanitise)
      |> String.intercalate "\n  - "
    let prog_str := prog.header.toStrings ++ prog.body.toStrings
      |> "\n\n".intercalate
    s!"-----  Calls  -----\n  {calls_str}\n
----- Strings -----\n  - {string_str}\n
----- Program -----\n\n{prog_str}\n
----- ------- -----\n"
