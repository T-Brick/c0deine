import C0deine.Utils.Symbol
import C0deine.Utils.Comparison

namespace C0deine.Ast

def Ident := Symbol
deriving ToString

inductive Typ
| int
| bool
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

inductive BinOp.Bool
| and | or

inductive BinOp
| int (op : BinOp.Int)
| cmp (op : Comparator)
| bool (op : BinOp.Bool)

inductive AsnOp
| eq | aseq (op : BinOp.Int)

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

inductive Stmt
| decl (type : Typ) (name : Ident) (init : Option Expr) (body : List Stmt)
| assn (lv : LValue) (op : AsnOp) (v : Expr)
| ite (cond : Expr) (tt : List Stmt) (ff : List Stmt)
| while (cond : Expr) (body : List Stmt)
| «return» (e : Option Expr)
| assert (e : Expr)
| exp (e : Expr)

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
  type : Option Typ
  name : Ident
  params : List Param
  body : List Stmt

structure FDecl where
  type : Option Typ
  name : Ident
  params : List Param

inductive GDecl
| fdecl : FDecl → GDecl
| fdef  : FDef  → GDecl
| tydef : TyDef → GDecl
| sdecl : SDecl → GDecl
| sdef  : SDef  → GDecl

def Prog := List GDecl
