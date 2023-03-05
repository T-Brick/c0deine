/-
  A Typed Syntax Tree, which is similar to the AST, but with expressions
  having typed annotations. Types are dealiased in this representation.
 -/
import C0deine.Utils.Symbol
import C0deine.Utils.Comparison
import C0deine.Type.Typ

namespace C0deine.Tst

universe u
-- todo: maybe we can restrict this to just be the types we want?
structure Typed (α : Type u) where
  typ : Typ.Check
  data : α

inductive UnOp.Int | neg | not
inductive UnOp.Bool | neg
inductive UnOp
| int (op : UnOp.Int)
| bool (op : UnOp.Bool)

inductive BinOp.Int
| plus | minus | times | div | mod | and | xor | or | lsh | rsh


inductive BinOp.Bool
| and | or

inductive BinOp
| int (op : BinOp.Int)
| cmp (op : Comparator)
| bool (op : BinOp.Bool)

inductive Expr
| num (v : UInt32)
| var (name : Symbol)
| «true» | «false»
| null
| unop (op : UnOp) (e : Typed Expr)
| binop (op : BinOp) (l r : Typed Expr)
| ternop (cond tt ff : Typed Expr)
| app (f : Symbol) (args : List (Typed Expr))
| alloc (ty : Typ)
| alloc_array (ty : Typ) (e : Typed Expr)
| dot (e : Typed Expr) (field : Symbol)
| deref (e : Typed Expr)
| index (e : Typed Expr) (index : Typed Expr)

inductive LValue
| var (name : Symbol)
| dot (lv : Typed LValue) (field : Symbol)
| deref (lv : Typed LValue)
| index (lv : Typed LValue) (index : Typed Expr)

inductive Stmt
| decl (name : Typed Symbol) (body : List Stmt)
| assign (lhs : Typed LValue) (rhs : Typed Expr)
| expr (e : Typed Expr)
| ite (cond : Typed Expr) (tt : Stmt) (ff : Stmt)
| while (cond : Typed Expr) (body : List Stmt)
| «return» (e : Option (Typed Expr))
| assert (e : Typed Expr)

structure SDef where
  name : Symbol
  fields : List (Typed Symbol)

structure FDef where
  type : Typ
  name : Symbol
  params : List (Typed Symbol)
  body : List Stmt

structure FDecl where
  type : Typ
  name : Symbol
  params : List (Typed Symbol)

inductive GDecl
| fdecl : FDecl → GDecl
| fdef  : FDef  → GDecl
| sdef  : SDef  → GDecl

def Prog := List GDecl
