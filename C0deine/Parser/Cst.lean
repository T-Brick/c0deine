import C0deine.Utils.Symbol

namespace C0deine.Ast

def Ident := Symbol
deriving ToString

inductive Typ
| int
| bool
| void
| tydef (name : Ident)
| ptr : Typ → Typ
| arr : Typ → Typ
| struct (name : Ident)

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

inductive AsnOp
| eq | aseq (op : BinOp.Int)

inductive PostOp
| incr | decr

inductive Expr
| num (v : UInt32)
| «true» | «false»
| null
| unop (op : UnOp) (e : Expr)
| binop (op : BinOp) (l r : Expr)
| ternop (cond : Expr) (tt : Expr) (ff : Expr)
| app (f : Ident) (args : List Expr)
| alloc (ty : Typ)
| alloc_array (ty : Typ) (e : Expr)
| var (name : Ident)
| dot (e : Expr) (field : Ident)
| arrow (e : Expr) (field : Ident)
| deref (e : Expr)
| index (e : Expr) (index : Expr)

inductive LValue
| var (name : Ident)
| dot (lv : LValue) (field : Ident)
| arrow (lv : LValue) (field : Ident)
| deref (lv : LValue)
| index (lv : LValue) (index : Expr)

mutual
inductive Control
| ite (cond : Expr) (tt : Stmt) (ff : Stmt)
| while (cond : Expr) (body : Stmt)
| «for» (init : Simp) (cond : Expr) (step : Simp)
| «return» (e : Option Expr)
| assert (e : Expr)

inductive Simp
| assn (lv : LValue) (op : AsnOp) (v : Expr)
| post (lv : LValue) (op : PostOp)
| decl (type : Typ) (name : Ident)
| exp (e : Expr)

inductive Stmt
| simp : Simp → Stmt
| ctrl : Control → Stmt
| block : List Stmt → Stmt
end

structure Field where
  type : Typ
  name : Ident

structure SDef where
  name : Ident
  fields : List Field

structure SDecl where
  name : Ident

structure TyDef where
  type : Typ
  name : Ident

structure Param where
  type : Typ
  name : Ident

structure FDef where
  type : Typ
  name : Ident
  params : List Param
  body : Block

structure FDecl where
  type : Typ
  name : Ident
  params : List Param

inductive GDecl
| fdecl : FDecl → GDecl
| fdef  : FDef  → GDecl
| tydef : TyDef → GDecl
| sdecl : SDecl → GDecl
| sdef  : SDef  → GDecl

def Prog := List GDecl
