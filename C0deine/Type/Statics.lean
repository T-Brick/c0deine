import C0deine.AuxDefs
import C0deine.Parser.Ast

namespace C0deine.Statics

open Ast

def _root_.C0deine.Ast.Typ.isResolved : Typ → Bool
| .int      => true
| .bool     => true
| .struct _ => true
| .ptr t    => t.isResolved
| .arr t    => t.isResolved
| .tydef _  => false

nonrec def Typ := { t : Typ // t.isResolved }

def Typ.int : Typ := ⟨.int, rfl⟩
def Typ.bool : Typ := ⟨.int, rfl⟩
def Typ.struct (name : Ident) : Typ := ⟨.struct name, rfl⟩
def Typ.ptr (t : Typ) : Typ := ⟨.ptr t.1, by unfold Typ.isResolved; exact t.2⟩
def Typ.arr (t : Typ) : Typ := ⟨.arr t.1, by unfold Typ.isResolved; exact t.2⟩

structure StructSig where
  fieldTys : Ident → Option Typ

structure FuncSig where
  arity : Nat
  argTys : Fin arity → Typ
  retTy : Option Typ
  defined : Bool

structure GCtx where
  struct : Ident → Option StructSig
  tydef : Ident → Option Typ
  func : Ident → Option FuncSig

def GCtx.empty : GCtx := {
  struct := fun _ => none
, tydef  := fun _ => none
, func   := fun _ => none
}

inductive TypResolves (Δ : GCtx) : Ast.Typ → Typ → Prop
| int    : TypResolves Δ .int .int
| bool   : TypResolves Δ .bool .bool
| struct : TypResolves Δ (.struct s) (.struct s)
| ptr t  : TypResolves Δ t τ → TypResolves Δ (.ptr t) (.ptr τ)
| arr t  : TypResolves Δ t τ → TypResolves Δ (.arr t) (.arr τ)
| tydef  : Δ.tydef t = some τ → TypResolves Δ (.tydef t) τ

inductive TypOptResolves (Δ : GCtx) : Option Ast.Typ → Option Typ → Prop
| none : TypOptResolves Δ none none
| some : TypResolves Δ t τ → TypOptResolves Δ (some t) (some τ)  

inductive UnopTc : Typ → UnOp → Prop
| int : UnopTc .int (.int op)
| bool : UnopTc .bool (.bool op)

inductive BinopTc : Typ → Typ → BinOp → Prop
| int : BinopTc .int .int (.int op)
| bool : BinopTc .bool .bool (.bool op)
| cmp : BinopTc .int .bool (.cmp cmp)

inductive ExprTc (Δ : GCtx) (Γ : Ident → Option Typ) : Expr → Typ → Prop
| num     : ExprTc Δ Γ (.num v) .int
| «true»  : ExprTc Δ Γ .«true»  .bool
| «false» : ExprTc Δ Γ .«true»  .bool
| null    : ExprTc Δ Γ .null (.ptr τ)
| unop
  : UnopTc i op → ExprTc Δ Γ e i →
    ExprTc Δ Γ (.unop op e) i
| binop
  : BinopTc i o op →
    ExprTc Δ Γ l i →
    ExprTc Δ Γ r i →
    ExprTc Δ Γ (.binop op l r) o
| ternop
  : ExprTc Δ Γ cc .bool →
    ExprTc Δ Γ tt τ →
    ExprTc Δ Γ ff τ →
    ExprTc Δ Γ (.ternop cc tt ff) τ
| app
  : Δ.func f = some sig → sig.retTy = some ρ →
    (h : sig.arity = args.length) →
    (∀ i, ExprTc Δ Γ (args[h ▸ i]) (sig.argTys i)) →
    ExprTc Δ Γ (.app f args) ρ
| alloc
  : TypResolves Δ ty τ →
    ExprTc Δ Γ (.alloc ty) (.ptr τ)
| alloc_array
  : TypResolves Δ ty τ →
    ExprTc Δ Γ e .int →
    ExprTc Δ Γ (.alloc_array ty e) (.arr τ)
| var
  : Γ name = some ty →
    ExprTc Δ Γ (.var name) ty
| dot
  : ExprTc Δ Γ e (.struct s) →
    Δ.struct s = some ssig → ssig.fieldTys f = some ty →
    ExprTc Δ Γ (.dot e f) ty
| arrow
  : ExprTc Δ Γ e (.ptr (.struct s)) →
    Δ.struct s = some ssig → ssig.fieldTys f = some ty →
    ExprTc Δ Γ (.arrow e f) ty
| deref
  : ExprTc Δ Γ e (.ptr ty) →
    ExprTc Δ Γ (.deref e) ty
| index
  : ExprTc Δ Γ e (.arr ty) →
    ExprTc Δ Γ idx .int →
    ExprTc Δ Γ (.index e idx) ty

inductive LValueTc (Δ : GCtx) (Γ : Ident → Option Typ) : LValue → Typ → Prop
| var : Γ name = some ty → LValueTc Δ Γ (.var name) ty
| dot
  : LValueTc Δ Γ lv (.struct name) → Δ.struct name = some ssig → ssig.fieldTys field = some ty →
    LValueTc Δ Γ (.dot lv field) ty
| arrow
  : LValueTc Δ Γ lv (.ptr (.struct name)) →
    Δ.struct name = some ssig → ssig.fieldTys field = some ty →
    LValueTc Δ Γ (.arrow lv field) ty
| deref
  : LValueTc Δ Γ lv (.ptr ty) →
    LValueTc Δ Γ (.deref lv) ty
| index
  : LValueTc Δ Γ lv (.arr ty) →
    ExprTc Δ Γ index .int →
    LValueTc Δ Γ (.index lv index) ty

mutual
inductive StmtTc (Δ : GCtx) : (Γ : Ident → Option Typ) → Stmt → Option Typ → Prop
| decl_noninit
  : Γ name = none →
    TypResolves Δ ty τ →
    StmtsTc Δ (Γ.update name (some τ)) body ρ →
    StmtTc Δ Γ (.decl ty name none body) ρ
| decl_init
  : Γ name = none → ExprTc Δ Γ init τ →
    TypResolves Δ ty τ →
    StmtsTc Δ (Γ.update name (some τ)) body ρ →
    StmtTc Δ Γ (.decl ty name (some init) body) ρ
| assn_eq
  : LValueTc Δ Γ lv τ → ExprTc Δ Γ v τ →
    StmtTc Δ Γ (.assn lv .eq v) ρ
| assn_op
  : LValueTc Δ Γ lv τ → BinopTc τ τ (.int op) → ExprTc Δ Γ v τ →
    StmtTc Δ Γ (.assn lv (.aseq op) v) ρ
| ite
  : ExprTc Δ Γ cc .bool →
    StmtsTc Δ Γ tt ρ →
    StmtsTc Δ Γ ff ρ →
    StmtTc Δ Γ (.ite cc tt ff) ρ
| while
  : ExprTc Δ Γ cc .bool →
    StmtsTc Δ Γ body ρ →
    StmtTc Δ Γ (.while cc body) ρ
| «return»
  : ExprTc Δ Γ e ρ →
    StmtTc Δ Γ (.return e) ρ
| assert
  : ExprTc Δ Γ e .bool →
    StmtTc Δ Γ (.assert e) ρ
| exp
  : ExprTc Δ Γ e τ →
    StmtTc Δ Γ (.exp e) ρ

inductive StmtsTc (Δ : GCtx) : (Γ : Ident → Option Typ) → List Stmt → Option Typ → Prop
| nil : StmtsTc Δ Γ [] ρ
| cons : StmtTc Δ Γ x ρ → StmtsTc Δ Γ xs ρ → StmtsTc Δ Γ (x::xs) ρ
end

inductive FuncSigCompat (Δ : GCtx) (name : Ident) (fs : FuncSig) : Prop
| new (hf : Δ.func name = none) (ht : Δ.tydef name = none)
| redecl  (h : Δ.func name = some fs')
          (h_arity : fs.arity = fs'.arity)
          (h_args : h_arity ▸ fs.argTys = fs'.argTys)
          (h_ret : fs.retTy = fs'.retTy)
          (h_def : ¬fs.defined ∨ ¬fs'.defined)

def mapOfList [DecidableEq α] : List (α × β) → (α → Option β)
| [] => fun _ => none
| (a,b)::L => (mapOfList L).update a (some b)

inductive GDeclTc : GCtx → GDecl → GCtx → Prop
| tydef
  : Δ.func td.name = none →
    Δ.tydef td.name = none →
    TypResolves Δ td.type τ →
    GDeclTc Δ (.tydef td) {Δ with tydef := Δ.tydef.update td.name τ}
| fdecl {τ : Fin f.params.length → Typ} {fs : FuncSig}
  : TypOptResolves Δ f.type ρ →
    (∀ i, TypResolves Δ (f.params.get i).type (τ i)) →
    (∀ i j, i ≠ j → (f.params.get i).name ≠ (f.params.get j).name) →
    fs = {
      arity := f.params.length
    , retTy := ρ
    , argTys := τ
    , defined := false
    } →
    FuncSigCompat Δ f.name fs →
    GDeclTc Δ (.fdecl f) {Δ with func := Δ.func.update f.name fs}
| fdef {τ : Fin f.params.length → Typ} {fs : FuncSig}
  : TypOptResolves Δ f.type ρ →
    (∀ i, TypResolves Δ f.params[i].type (τ i)) →
    (∀ (i j : Fin f.params.length), i ≠ j → f.params[i].name ≠ f.params[j].name) →
    fs = {
      arity := f.params.length
    , retTy := ρ
    , argTys := τ
    , defined := true
    } →
    FuncSigCompat Δ f.name fs →
    StmtsTc Δ (mapOfList (List.ofFn (fun i => (f.params[i].name, τ i)))) f.body ρ →
    GDeclTc Δ (.fdef f) {Δ with func := Δ.func.update f.name (some {
      arity := f.params.length
    , retTy := ρ
    , argTys := τ
    , defined := true
    })}
-- this rule is correct; sdecls are genuinely meaningless
| sdecl : GDeclTc Δ (.sdecl s) Δ
| sdef {τ : Fin s.fields.length → Typ}
  : Δ.struct s.name = none →
    (∀ (i j : Fin s.fields.length), i ≠ j → s.fields[i].name ≠ s.fields[j].name) →
    (∀ i, TypResolves Δ s.fields[i].type (τ i)) →
    GDeclTc Δ (.sdef s) {Δ with struct := Δ.struct.update s.name (some ⟨
      mapOfList (List.ofFn (fun i => (s.fields[i].name, τ i)))⟩)}

inductive GDeclsTc : GCtx → List GDecl → GCtx → Prop
| nil : GDeclsTc Δ [] Δ
| cons : GDeclTc Δ gd Δ' → GDeclsTc Δ' gds Δ'' → GDeclsTc Δ (gd :: gds) Δ''

def validInHeader : GDecl → Bool
| .sdef _ | .sdecl _ | .tydef _ | .fdecl _ => true
| .fdef _ => false

structure ProgTc (p : Prog) where
  header_decls_only : ∀ gd ∈ p.header, validInHeader gd
  header_ctx : GCtx
  header_tc : GDeclsTc .empty p.header header_ctx
  prog_ctx : GCtx
  prog_tc : GDeclsTc header_ctx p.program prog_ctx
