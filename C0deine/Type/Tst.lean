import C0deine.Parser.Ast

namespace C0deine.Tst

def Ident := Ast.Ident

inductive Typ
| int
| bool
| void
| ptr : Typ → Typ
| arr : Typ → Typ
| struct (name : Ident)

universe u

structure Typed (α : Type u) where
  typ : Typ
  data : α

inductive LValue
| var (name : Ident)
| dot (lv : Typed LValue) (field : Ident)
| arrow (lv : Typed LValue) (field : Ident)
| deref (lv : Typed LValue)
| index (lv : Typed LValue) (index : Typed Expr)

inductive UnOp.Int | neg | not
inductive UnOp.Bool | neg
inductive UnOp
| int (op : UnOp.Int)
| bool (op : UnOp.Bool)

inductive BinOp.Int
| plus | minus | times | div | mod | and | xor | or | lsh | rsh

inductive BinOp.Cmp
| lt | le | gt | ge | eq | ne

inductive BinOp.Bool
| and | or

inductive BinOp
| int (op : BinOp.Int)
| cmp (op : BinOp.Cmp)
| bool (op : BinOp.Bool)

inductive Expr
| num (v : UInt32)
| var (name : Ident)
| «true» | «false»
| null
| unop (op : UnOp) (e : Typed Expr)
| binop (op : BinOp) (l r : Typed Expr)
| ternop (cond : Typed Expr) (tt : Typed Expr) (ff : Typed Expr)
| app (f : Ident) (args : List (Typed Expr))
| alloc (ty : Typ)
| alloc_array (ty : Typ) (e : Typed Expr)
| dot (e : Typed Expr) (field : Ident)
| deref (e : Typed Expr)
| index (e : Typed Expr) (index : Typed Expr)

inductive Stmt
| decl (name : Typed Ident) (body : List Stmt)
| assign (lhs : Typed LValue) (rhs : Typed Expr)
| expr (e : Typed Expr)
| ite (cond : Typed Expr) (tt : Stmt) (ff : Stmt)
| while (cond : Typed Expr) (body : List Stmt)
| «return» (e : Option (Typed Expr))
| assert (e : Typed Expr)

structure SDef where
  name : Ident
  fields : List (Typed Ident)

structure FDef where
  type : Typ
  name : Ident
  params : List (Typed Ident)
  body : Stmt

structure FDecl where
  type : Typ
  name : Ident
  params : List (Typed Ident)

inductive GDecl
| fdecl : FDecl → GDecl
| fdef  : FDef  → GDecl
| sdef  : SDef  → GDecl

def Prog := List GDecl
