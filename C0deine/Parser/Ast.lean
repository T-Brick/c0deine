import C0deine.Utils.Comparison
import C0deine.Utils.Int32
import C0deine.Utils.Symbol

namespace C0deine.Ast

def Ident := Symbol
deriving ToString, DecidableEq

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
| num (v : Int32)
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
| sdecl : SDecl → GDecl
| sdef  : SDef  → GDecl

structure Prog where
  header : List GDecl
  program : List GDecl


def Typ.toString : Typ → String
  | .int => "int"
  | .bool => "bool"
  | .tydef (name : Ident) => s!"alias {name}"
  | .ptr ty => s!"{ty.toString}*"
  | .arr ty => s!"{ty.toString}[]"
  | .struct (name : Ident) => s!"struct {name}"
instance : ToString Typ where toString := Typ.toString
instance : ToString (Option Typ) where
  toString | none => "void" | some t => s!"{t}"


def UnOp.Int.toString : UnOp.Int → String
  | neg => "~"
  | not => "!"
instance : ToString UnOp.Int where toString := UnOp.Int.toString

def UnOp.Bool.toString : UnOp.Bool → String
  | neg => "!"
instance : ToString UnOp.Bool where toString := UnOp.Bool.toString

def UnOp.toString : UnOp → String
  | int op  => s!"{op}"
  | bool op => s!"{op}"
instance : ToString UnOp where toString := UnOp.toString


def BinOp.Int.toString : BinOp.Int → String
  | plus => "+"
  | minus => "-"
  | times => "*"
  | div => "/"
  | mod => "%"
  | and => "&"
  | xor => "^"
  | or => "|"
  | lsh => "<<"
  | rsh => ">>"
instance : ToString BinOp.Int where toString := BinOp.Int.toString

def BinOp.Bool.toString : BinOp.Bool → String
  | .and => "&&"
  | .or  => "||"
instance : ToString BinOp.Bool where toString := BinOp.Bool.toString

def BinOp.toString : BinOp → String
  | int op  => s!"{op}"
  | cmp op  => s!"{op}"
  | bool op => s!"{op}"
instance : ToString BinOp where toString := BinOp.toString


def AsnOp.toString : AsnOp → String
  | eq  => s!"="
  | aseq op  => s!"{op}="
instance : ToString AsnOp where toString := AsnOp.toString

mutual
def Expr.toString : Expr → String
  | num v => s!"{v}"
  | «true» => "true"
  | «false» => "false"
  | null => "NULL"
  | unop op e => s!"{op}({e.toString})"
  | binop op l r => s!"({l.toString}) {op} ({r.toString})"
  | ternop c tt ff => s!"({c.toString}) ? ({tt.toString}) : ({ff.toString})"
  | app f args => s!"{f}({Expr.argsToString args})"
  | alloc ty => s!"alloc({ty})"
  | alloc_array ty e => s!"alloc_array({ty}, {e.toString})"
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
  | .decl type name init body =>
    let initStr :=
      match init with
      | none => ""
      | some i => s!", {i}"
    s!"declare({type}, {name}{initStr}, {Stmt.listToString body}\n\t)"
  | .assn lv op v => s!"{lv} {op} {v}"
  | .ite cond tt ff =>
    s!"if({cond}){Stmt.listToString tt}\nelse\n{Stmt.listToString ff}\nendif\n"
  | .while cond body => s!"while({cond})\n{Stmt.listToString body}\nendwhile\n"
  | .«return» .none => "return"
  | .«return» (.some e) => s!"return {e}"
  | .assert e => s!"assert({e})"
  | .exp e => s!"{e}"

def Stmt.listToString (stmts : List Stmt) : String :=
  match stmts with
  | [] => ""
  | stmt :: stmts =>
    s!"\n\t{Stmt.toString stmt};" |>.append (Stmt.listToString stmts)
end

instance : ToString Stmt        where toString := Stmt.toString
instance : ToString (List Stmt) where toString := Stmt.listToString

def Stmt.toPrettyString (s : Stmt) : String :=
  match s with
  | .decl type name init _body =>
    let initStr :=
      match init with
      | none => ""
      | some i => s!" = {i}"
    s!"{type} {name}{initStr};"
  | .ite cond _tt _ff => s!"if({cond}) ..."
  | .while cond _body => s!"while({cond}) ..."
  | _ => s.toString

instance : ToString Field where toString f := s!"{f.type} {f.name};"
instance : ToString (List Field) where
  toString fs := "{\n\t".append (fs.foldr (fun f acc => s!"\t{f}\n{acc}") "}")

instance : ToString SDef where toString s := s!"struct {s.name} {s.fields};"
instance : ToString SDecl where toString s := s!"struct {s.name};"

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
  | .sdecl s => s!"{s}"
  | .sdef  s => s!"{s}"
instance : ToString GDecl where toString := GDecl.toString

instance : ToString Prog where
  toString prog :=
    "---------\nHeader:\n---------\n\n"
    |>.append (String.intercalate "\n\n" (prog.header.map GDecl.toString))
    |>.append "\n\n---------\nSource:\n---------\n\n"
    |>.append (String.intercalate "\n\n" (prog.program.map GDecl.toString))
