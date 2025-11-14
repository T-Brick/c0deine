import C0deine.Utils.Comparison
import C0deine.Context.Symbol
import C0deine.Type.Typ
import C0deine.Type.Tst
import Numbers

namespace C0deine.Pst

open Typ
open Numbers

inductive Expr
| num : Numbers.Int32 → Expr
| char : Char → Expr
| str : String → Expr
| var : Symbol → Expr
| «true» : Expr
| «false» : Expr
| null : Expr
| unop_int : Tst.UnOp.Int → Typed Expr → Expr
| unop_bool : Tst.UnOp.Bool → Typed Expr → Expr
| binop_int : Tst.BinOp.Int → Typed Expr → Typed Expr → Expr
| binop_bool : Tst.BinOp.Bool → Typed Expr → Typed Expr → Expr
| binop_eq : Comparator → Typed Expr → Typed Expr → Expr
| binop_rel_int : Comparator → Typed Expr → Typed Expr → Expr
| binop_rel_char : Comparator → Typed Expr → Typed Expr → Expr
| ternop : Typed Expr → Typed Expr → Typed Expr → Expr
| app : Symbol → List (Typed Expr) → Expr
| alloc : Typ → Expr
| alloc_array : Typ → Typed Expr → Expr
| dot : Typed Expr → Symbol → Expr
| deref : Typed Expr → Expr
| index : Typed Expr → Typed Expr → Expr
| result : Expr
| length : Typed Expr → Expr

inductive LValue
| var : Symbol → LValue
| dot : Typed LValue → Symbol → LValue
| deref : Typed LValue → LValue
| index : Typed LValue → Typed Expr → LValue

inductive Anno
| requires : Typed Expr → Anno
| ensures : Typed Expr → Anno
| loop_invar : Typed Expr → Anno
| assert : Typed Expr → Anno

inductive Stmt
| decl : Symbol → List Stmt → Stmt
| decl_init : Symbol → Typed Expr → List Stmt → Stmt
| assign_var : Typed LValue → Typed Expr → Stmt
| assign : Typed LValue → Typed Expr → Stmt
| asnop : Typed LValue → Tst.BinOp.Int → Typed Expr → Stmt
| expr : Typed Expr → Stmt
| ite : Typed Expr → List Stmt → List Stmt → Stmt
| while : Typed Expr → List Anno → List Stmt → Stmt
| return_void : Stmt
| return_tau : Typed Expr → Stmt
| assert : Typed Expr → Stmt
| error : Typed Expr → Stmt
| anno : Anno → Stmt

structure SDef where
  name : Symbol
  fields : List (Typed Symbol)

structure FDef where
  type : Option Typ
  name : Symbol
  params : List (Typed Symbol)
  annos : List Anno
  body : List Stmt

structure FDecl where
  ret : Option Typ
  name : Symbol
  params : List Typ
  annos : List Anno

inductive GDecl
| fdecl : FDecl → GDecl
| fdef : FDef → GDecl
| sdef : SDef → GDecl


structure Prog where
  header : List GDecl
  body : List GDecl
  calls : Tst.Calls
  strings : List String

mutual
def Expr.ofTst : Tst.Expr Δ Γ τ → Typed Expr
| .num _ i => ⟨τ, .num i⟩
| .char _ c => ⟨τ, .char c⟩
| .str _ s => ⟨τ, .str s⟩
| .var x _ => ⟨τ, .var x⟩
| .true _ => ⟨τ, .true⟩
| .false _ => ⟨τ, .false⟩
| .null _ => ⟨τ, .null⟩
| .unop_int _ _ op e => ⟨τ, .unop_int op (ofTst e)⟩
| .unop_bool _ _ op e => ⟨τ, .unop_bool op (ofTst e)⟩
| .binop_int _ _ _ op l r => ⟨τ, .binop_int op (ofTst l) (ofTst r)⟩
| .binop_bool _ _ _ op l r => ⟨τ, .binop_bool op (ofTst l) (ofTst r)⟩
| .binop_eq _ op _ l r _ _ => ⟨τ, .binop_eq op (ofTst l) (ofTst r)⟩
| .binop_rel_int _ _ _ op _ l r => ⟨τ, .binop_rel_int op (ofTst l) (ofTst r)⟩
| .binop_rel_char _ _ _ op _ l r => ⟨τ, .binop_rel_char op (ofTst l) (ofTst r)⟩
| .ternop _ _ c t f _ => ⟨τ, .ternop (ofTst c) (ofTst t) (ofTst f)⟩
| .app (status:=status) f _ _ _ args =>
    
    sorry
| .alloc τ' => ⟨τ, .alloc τ'⟩
| .alloc_array _ τ' e => ⟨τ, .alloc_array τ' (ofTst e)⟩
| .dot _ e f _ _ => ⟨τ, .dot (ofTst e) f⟩
| .deref _ e => ⟨τ, .deref (ofTst e)⟩
| .index _ _ a i => ⟨τ, .index (ofTst a) (ofTst i)⟩
| .result _ => ⟨τ, .result⟩
| .length _ e => ⟨τ, .length (ofTst e)⟩

-- def convertArgs (acc : List (Typed Expr)) : Unit := sorry

end
