/- C0deine - Statics
   An encoding of the static semantics of C0 programs (in the AST).
   - James Gallicchio
   - Thea Brick
 -/
import C0deine.AuxDefs
import C0deine.Ast.Ast

namespace C0deine.Statics

open Ast

def _root_.C0deine.Ast.Typ.isResolved : Typ → Bool
| .int      => true
| .char     => true
| .string   => true
| .bool     => true
| .struct _ => true
| .ptr t    => t.isResolved
| .arr t    => t.isResolved
| .tydef _  => false

nonrec def Typ := { t : Typ // t.isResolved }

@[reducible] def Typ.int    : Typ := ⟨.int   , rfl⟩
@[reducible] def Typ.char   : Typ := ⟨.char  , rfl⟩
@[reducible] def Typ.string : Typ := ⟨.string, rfl⟩
@[reducible] def Typ.bool   : Typ := ⟨.bool  , rfl⟩
@[reducible] def Typ.struct (name : Ident) : Typ := ⟨.struct name, rfl⟩
@[reducible] def Typ.ptr (t : Typ) : Typ := ⟨.ptr t.1, by unfold Typ.isResolved; exact t.2⟩
@[reducible] def Typ.arr (t : Typ) : Typ := ⟨.arr t.1, by unfold Typ.isResolved; exact t.2⟩

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

def GCtx.empty : GCtx :=
  { struct := fun _ => none
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
| int  : UnopTc .int (.int op)
| bool : UnopTc .bool (.bool op)

inductive BinopTc : Typ → Typ → BinOp → Prop
| int  : BinopTc .int .int (.int op)
| bool : BinopTc .bool .bool (.bool op)
| cmp  : BinopTc .int .bool (.cmp op)

-- Used for representing the context of where an expression is? For instance,
--  if an expression is in a ensures annotation, outside of an annotation.
inductive ExprLang
| ensures : (ret : Option Typ) → ExprLang
| other_anno
| non_anno

inductive ExprLang.IsAnno : ExprLang → Prop
| ensures    : IsAnno (.ensures ret)
| other_anno : IsAnno .other_anno

inductive FullExprTc (Δ : GCtx) (Γ : Ident → Option Typ)
    : (exprLang : ExprLang) → Expr → Typ → Prop
| num     : FullExprTc Δ Γ exprLang (.num v)  .int
| char    : FullExprTc Δ Γ exprLang (.char c) .char
| str     : FullExprTc Δ Γ exprLang (.str s)  .string
| «true»  : FullExprTc Δ Γ exprLang .true     .bool
| «false» : FullExprTc Δ Γ exprLang .false    .bool
| null    : FullExprTc Δ Γ exprLang .null (.ptr τ)
| unop
  : UnopTc i op
  → FullExprTc Δ Γ exprLang e i
  → FullExprTc Δ Γ exprLang (.unop op e) i
| binop
  : BinopTc i o op
  → FullExprTc Δ Γ exprLang l i
  → FullExprTc Δ Γ exprLang r i
  → FullExprTc Δ Γ exprLang (.binop op l r) o
| ternop
  : FullExprTc Δ Γ exprLang cc .bool
  → FullExprTc Δ Γ exprLang tt τ
  → FullExprTc Δ Γ exprLang ff τ
  → FullExprTc Δ Γ exprLang (.ternop cc tt ff) τ
| app
  : Δ.func f = some sig
  → sig.retTy = some ρ
  → (h : sig.arity = args.length)
  → (∀ i, FullExprTc Δ Γ exprLang (args[h ▸ i]) (sig.argTys i))
  → FullExprTc Δ Γ exprLang (.app f args) ρ
| alloc
  : TypResolves Δ ty τ
  → FullExprTc Δ Γ exprLang (.alloc ty) (.ptr τ)
| alloc_array
  : TypResolves Δ ty τ
  → FullExprTc Δ Γ exprLang e .int
  → FullExprTc Δ Γ exprLang (.alloc_array ty e) (.arr τ)
| var
  : Γ name = some ty
  → FullExprTc Δ Γ exprLang (.var name) ty
| dot
  : FullExprTc Δ Γ exprLang e (.struct s)
  → Δ.struct s = some ssig
  → ssig.fieldTys f = some ty
  → FullExprTc Δ Γ exprLang (.dot e f) ty
| arrow
  : FullExprTc Δ Γ exprLang e (.ptr (.struct s))
  → Δ.struct s = some ssig
  → ssig.fieldTys f = some ty
  → FullExprTc Δ Γ exprLang (.arrow e f) ty
| deref
  : FullExprTc Δ Γ exprLang e (.ptr ty)
  → FullExprTc Δ Γ exprLang (.deref e) ty
| index
  : FullExprTc Δ Γ exprLang e (.arr ty)
  → FullExprTc Δ Γ exprLang idx .int
  → FullExprTc Δ Γ exprLang (.index e idx) ty
| result : FullExprTc Δ Γ (.ensures (.some τ)) .result τ
| length
  : ExprLang.IsAnno exprLang
  → FullExprTc Δ Γ exprLang e (.arr τ)
  → FullExprTc Δ Γ exprLang (.length e) .int

abbrev ExprTc := fun Δ Γ => FullExprTc Δ Γ .non_anno

inductive LValueTc (Δ : GCtx) (Γ : Ident → Option Typ) : LValue → Typ → Prop
| var : Γ name = some ty → LValueTc Δ Γ (.var name) ty
| dot
  : LValueTc Δ Γ lv (.struct name)
  → Δ.struct name = some ssig
  → ssig.fieldTys field = some ty
  → LValueTc Δ Γ (.dot lv field) ty
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

inductive AnnoTc.Loop (Δ : GCtx) (Γ : Ident → Option Typ) : List Anno → Prop
| nil  : AnnoTc.Loop Δ Γ []
| cons : FullExprTc Δ Γ .other_anno e .bool
       → AnnoTc.Loop Δ Γ as
       → AnnoTc.Loop Δ Γ (.loop_invar e :: as)

inductive AnnoTc.Func (Δ : GCtx) (Γ : Ident → Option Typ) (ret : Option Typ) : List Anno → Prop
| nil : AnnoTc.Func Δ Γ ret []
| cons_requires
  : FullExprTc Δ Γ .other_anno e .bool
  → AnnoTc.Func Δ Γ ret as
  → AnnoTc.Func Δ Γ ret (.requires e :: as)
| cons_ensures
  : FullExprTc Δ Γ (.ensures ret) e .bool
  → AnnoTc.Func Δ Γ ret as
  → AnnoTc.Func Δ Γ ret (.ensures e :: as)

inductive AnnoTc.Free (Δ : GCtx) (Γ : Ident → Option Typ) : List Anno → Prop
| nil  : AnnoTc.Free Δ Γ []
| cons : FullExprTc Δ Γ .other_anno e .bool
       → AnnoTc.Free Δ Γ as
       → AnnoTc.Free Δ Γ (.requires e :: as)

mutual
inductive StmtTc (Δ : GCtx) : (Γ : Ident → Option Typ) → Stmt → Option Typ → Prop
| decl_noninit
  : Γ name = none
  → TypResolves Δ ty τ
  → StmtsTc Δ (Function.update Γ name (some τ)) body ρ
  → StmtTc Δ Γ (.decl ty name none body) ρ
| decl_init
  : Γ name = none
  → ExprTc Δ Γ init τ
  → TypResolves Δ ty τ
  → StmtsTc Δ (Function.update Γ name (some τ)) body ρ
  → StmtTc Δ Γ (.decl ty name (some init) body) ρ
| assn_eq
  : LValueTc Δ Γ lv τ
  → ExprTc Δ Γ v τ
  → StmtTc Δ Γ (.assn lv .eq v) ρ
| assn_op
  : LValueTc Δ Γ lv τ
  → BinopTc τ τ (.int op)
  → ExprTc Δ Γ v τ
  → StmtTc Δ Γ (.assn lv (.aseq op) v) ρ
| ite
  : ExprTc Δ Γ cc .bool
  → StmtsTc Δ Γ tt ρ
  → StmtsTc Δ Γ ff ρ
  → StmtTc Δ Γ (.ite cc tt ff) ρ
| while
  : ExprTc Δ Γ cc .bool
  → StmtsTc Δ Γ body ρ
  → AnnoTc.Loop Δ Γ annos
  → StmtTc Δ Γ (.while cc annos body) ρ
| «return»
  : ExprTc Δ Γ e ρ
  → StmtTc Δ Γ (.return e) ρ
| assert
  : ExprTc Δ Γ e .bool
  → StmtTc Δ Γ (.assert e) ρ
| exp
  : ExprTc Δ Γ e τ
  → StmtTc Δ Γ (.exp e) ρ

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
| (a,b)::L => Function.update (mapOfList L) a (some b)

inductive GDeclTc : GCtx → GDecl → GCtx → Prop
| tydef
  : Δ.func td.name = none
  → Δ.tydef td.name = none
  → TypResolves Δ td.type τ
  → GDeclTc Δ (.tydef td) {Δ with tydef := Function.update Δ.tydef td.name τ}
| fdecl {τ : Fin f.params.length → Typ} {fs : FuncSig}
  : TypOptResolves Δ f.type ρ
  → (∀ i, TypResolves Δ (f.params.get i).type (τ i))
  → (∀ i j, i ≠ j → (f.params.get i).name ≠ (f.params.get j).name)
  → fs = { arity := f.params.length
         , retTy := ρ
         , argTys := τ
         , defined := false
         }
  → FuncSigCompat Δ f.name fs
  → AnnoTc.Func Δ (mapOfList (List.ofFn (fun i => (f.params[i].name, τ i)))) ρ f.annos
  → GDeclTc Δ (.fdecl f) {Δ with func := Function.update Δ.func f.name fs}
| fdef {τ : Fin f.params.length → Typ} {fs : FuncSig}
  : TypOptResolves Δ f.type ρ
  → (∀ i, TypResolves Δ f.params[i].type (τ i))
  → (∀ (i j : Fin f.params.length), i ≠ j → f.params[i].name ≠ f.params[j].name)
  → fs = { arity := f.params.length
         , retTy := ρ
         , argTys := τ
         , defined := true
         }
  → FuncSigCompat Δ f.name fs
  → AnnoTc.Func Δ (mapOfList (List.ofFn (fun i => (f.params[i].name, τ i)))) ρ f.annos
  → StmtsTc Δ (mapOfList (List.ofFn (fun i => (f.params[i].name, τ i)))) f.body ρ
  → GDeclTc Δ (.fdef f) {Δ with func := Function.update Δ.func f.name (some
    { arity := f.params.length
    , retTy := ρ
    , argTys := τ
    , defined := true
    })}
-- this rule is correct; sdecls are genuinely meaningless
| sdecl : GDeclTc Δ (.sdecl s) Δ
| sdef {τ : Fin s.fields.length → Typ}
  : Δ.struct s.name = none
  → (∀ (i j : Fin s.fields.length), i ≠ j → s.fields[i].name ≠ s.fields[j].name)
  → (∀ i, TypResolves Δ s.fields[i].type (τ i))
  → GDeclTc Δ (.sdef s) {Δ with struct := Function.update Δ.struct s.name (
      some ⟨ mapOfList (List.ofFn (fun i => (s.fields[i].name, τ i))) ⟩
    )}

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
