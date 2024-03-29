/- C0deine - C
   C language to be compiled with gcc/clang. Intended to be generated from a
   high-level IR tree.
   - James Gallicchio
-/
import C0deine.Context.Symbol
import C0deine.Context.Label
import C0deine.Utils.Comparison

namespace C0deine.Target.C

def Ident := Symbol
deriving ToString, DecidableEq

inductive Typ
| int
| void_ptr
| ptr : Typ → Typ
| arr : Typ → Typ
| tydef (name : Ident)
| struct (name : Ident)

inductive UnOp | neg | not | bnot

inductive BinOp.Int
| plus | minus | times | div | mod | and | xor | or | lsh | rsh

inductive BinOp.Bool
| band | bor

inductive BinOp
| int (op : BinOp.Int)
| bool (op : BinOp.Bool)
| cmp (cmp : Comparator)

inductive AsnOp
| eq | aseq (op : BinOp.Int)

inductive Expr
| num (v : Int)
| null
| unop (op : UnOp) (e : Expr)
| binop (op : BinOp) (l r : Expr)
| ternop (cond : Expr) (tt : Expr) (ff : Expr)
| app (f : Ident) (args : List Expr)
| sizeof (ty : Typ)
| calloc (size : Expr) (len : Expr)
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
| decl (type : Typ) (name : Ident)
| assn (lv : LValue) (op : AsnOp) (v : Expr)
| ite (cond : Expr) (tt : List Stmt) (ff : List Stmt)
| while (cond : Expr) (body : List Stmt)
| «return» (e : Option Expr)
| exp (e : Expr)

structure Field where
  type : Typ
  name : Ident

structure SDef where
  name : Ident
  fields : List Field

structure TyDef where
  type : Typ
  name : Ident

structure Param where
  type : Typ
  name : Ident

structure FDecl where
  type : Option Typ
  name : Ident
  params : List Param

structure FDef extends FDecl where
  body : List Stmt

inductive GDecl
| fdecl : FDecl → GDecl
| fdef  : FDef  → GDecl
| tydef : TyDef → GDecl
| sdef  : SDef  → GDecl

structure Prog where
  program : List GDecl


def Typ.toString : Typ → String
  | .int => "int"
  | .void_ptr => "void*"
  | .ptr ty => s!"{ty.toString}*"
  | .arr ty => s!"{ty.toString}[]"
  | .tydef (name : Ident) => s!"{name}"
  | .struct (name : Ident) => s!"struct {name}"
instance : ToString Typ where toString := Typ.toString

def UnOp.toString : UnOp → String
  | .neg => "-"
  | .not => "~"
  | .bnot => "!"
instance : ToString UnOp where toString := UnOp.toString

def BinOp.Int.toString : BinOp.Int → String
  | .plus   => "+"
  | .minus  => "-"
  | .times  => "*"
  | .div    => "/"
  | .mod    => "%"
  | .and    => "&"
  | .xor    => "^"
  | .or     => "|"
  | .lsh    => "<<"
  | .rsh    => ">>"
instance : ToString BinOp.Int where toString := BinOp.Int.toString

def BinOp.Bool.toString : BinOp.Bool → String
  | .band   => "&&"
  | .bor    => "||"
instance : ToString BinOp.Bool where toString := BinOp.Bool.toString

def BinOp.toString : BinOp → String
  | .int  op  => s!"{op}"
  | .bool op  => s!"{op}"
  | .cmp  op  => s!"{op}"
instance : ToString BinOp where toString := BinOp.toString


def AsnOp.toString : AsnOp → String
  | eq  => s!"="
  | aseq op  => s!"{op}="
instance : ToString AsnOp where toString := AsnOp.toString

mutual
def Expr.toString : Expr → String
  | num v => s!"{v}"
  | null => "NULL"
  | unop op e => s!"{op}({e.toString})"
  | binop op l r => s!"({l.toString}) {op} ({r.toString})"
  | ternop c tt ff => s!"({c.toString}) ? ({tt.toString}) : ({ff.toString})"
  | app f args => s!"{f}({Expr.argsToString args})"
  | sizeof ty => s!"sizeof({ty})"
  | calloc size elems => s!"calloc({size.toString}, {elems.toString})"
  | var name => s!"{name}"
  | dot e field => s!"({e.toString}).{field}"
  | arrow e field => s!"({e.toString})->{field}"
  | deref e => s!"*({e.toString})"
  | index e i => s!"({e.toString})[{i.toString}]"

def Expr.argsToString : List Expr → String
  | [] => ""
  | arg :: [] => s!"{arg.toString}"
  | arg :: args => s!"{arg.toString}, {Expr.argsToString args}"
end
instance : ToString Expr where toString := Expr.toString


def LValue.toString : LValue → String
  | var name => s!"{name}"
  | dot e field => s!"({e.toString}).{field}"
  | arrow e field => s!"({e.toString})->{field}"
  | deref e => s!"*({e.toString})"
  | index e i => s!"({e.toString})[{i.toString}]"
instance : ToString LValue where toString := LValue.toString

mutual
def Stmt.toString (s : Stmt) : String :=
  match s with
  | .decl type name   => s!"{type} {name};"
  | .assn lv op v     => s!"{lv} {op} {v};"
  | .ite cond tt ff   =>
    s!"if ({cond}) {blockToString tt} else {blockToString ff}"
  | .while cond body  => s!"while ({cond}) {blockToString body}"
  | .«return» .none   => "return;"
  | .«return» (.some e) => s!"return {e};"
  | .exp e => s!"{e};"

def Stmt.blockToString (stmts : List Stmt) : String :=
  match stmts with
  | [] => "{}"
  | [s] => toString s
  | s::ss =>
    "{\n" ++ toString s ++ listToString ss ++ "\n}"

def Stmt.listToString (stmts : List Stmt) : String :=
  match stmts with
  | [] => ""
  | stmt :: stmts =>
    s!"\n\t{toString stmt}" |>.append (listToString stmts)
end

instance : ToString Stmt        where toString := Stmt.toString
instance : ToString (List Stmt) where toString := Stmt.listToString

instance : ToString Field where toString f := s!"{f.type} {f.name};"
instance : ToString (List Field) where
  toString fs := "{\n\t".append (fs.foldr (fun f acc => s!"\t{f}\n{acc}") "}")

instance : ToString SDef where toString s := s!"struct {s.name} {s.fields};"

instance : ToString TyDef where toString t := s!"typedef {t.type} {t.name};"

instance : ToString Param where toString p := s!"{p.type} {p.name}"
instance : ToString (List Param) where
  toString ps := String.intercalate ", " (ps.map (fun p => s!"{p}"))

instance : ToString FDecl where toString f := s!"{f.type} {f.name}({f.params})"
instance : ToString FDef where
  toString f := s!"{f.type} {f.name}({f.params}) {f.body}"

def GDecl.toString : GDecl → String
  | .fdecl f => s!"{f}"
  | .fdef  f => s!"{f}"
  | .tydef t => s!"{t}"
  | .sdef  s => s!"{s}"
instance : ToString GDecl where toString := GDecl.toString

instance : ToString Prog where
  toString prog := String.intercalate "\n\n" (prog.program.map GDecl.toString)
