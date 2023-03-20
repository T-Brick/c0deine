/-
  A Typed Syntax Tree, which is similar to the AST, but with expressions
  having typed annotations. Types are dealiased in this representation.
 -/
import C0deine.Utils.Symbol
import C0deine.Utils.Comparison
import C0deine.Type.Typ

namespace C0deine.Tst

-- todo: maybe we can restrict this to just be the types we want?
inductive Typed (α : Type) where
  | typed (typ : Typ.Check) (data : α)

def Typed.data : Typed α → α
  | typed _typ data => data
def Typed.typ : Typed α → Typ.Check
  | typed typ _data => typ

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
| decl (name : Typed Symbol) (init : Option (Typed Expr)) (body : List Stmt)
| assign (lhs : Typed LValue) (op : Option BinOp.Int) (rhs : Typed Expr)
| expr (e : Typed Expr)
| ite (cond : Typed Expr) (tt : List Stmt) (ff : List Stmt)
| while (cond : Typed Expr) (body : List Stmt)
| «return» (e : Option (Typed Expr))
| assert (e : Typed Expr)

structure SDef where
  name : Symbol
  fields : List (Typed Symbol)

structure FDef where
  type : Option Typ
  name : Symbol
  params : List (Typed Symbol)
  body : List Stmt

structure FDecl where
  ret : Option Typ
  name : Symbol
  params : List Typ

inductive GDecl
| fdecl : FDecl → GDecl
| fdef  : FDef  → GDecl
| sdef  : SDef  → GDecl

def Prog := List GDecl


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

mutual
def Expr.toString : Expr → String
  | .num v => s!"{v}"
  | .«true» => "true"
  | .«false» => "false"
  | .null => "NULL"
  | .unop op e => s!"{op}{Expr.typedToString e}"
  | .binop op l r => s!"{Expr.typedToString l} {op} {Expr.typedToString r}"
  | .ternop c tt ff =>
    s!"{Expr.typedToString c} ? {Expr.typedToString tt} : {Expr.typedToString ff}"
  | .app f args => s!"{f}({Expr.argsToString args})"
  | .alloc ty => s!"alloc({ty})"
  | .alloc_array ty e => s!"alloc_array({ty}, {Expr.typedToString e})"
  | .var name => s!"{name}"
  | .dot e field => s!"{Expr.typedToString e}.{field}"
  | .deref e => s!"*{Expr.typedToString e}"
  | .index e i => s!"{Expr.typedToString e}[{Expr.typedToString i}]"

def Expr.argsToString : List (Typed Expr) → String
  | [] => ""
  | arg :: [] => s!"{Expr.typedToString arg}"
  | arg :: args => s!"{Expr.typedToString arg}, {Expr.argsToString args}"

def Expr.typedToString : Typed Expr → String
  | .typed typ data => s!"({Expr.toString data} : {typ})"
end

instance : ToString Expr where toString := Expr.toString
instance : ToString (Typed Expr) where toString := Expr.typedToString

mutual
def LValue.toString : LValue → String
  | var name => s!"{name}"
  | dot e field => s!"({LValue.typedToString e}).{field}"
  | deref e => s!"*({LValue.typedToString e})"
  | index e i => s!"({LValue.typedToString e})[{i}]"

def LValue.typedToString : Typed LValue → String
  | .typed typ data => s!"({LValue.toString data} : {typ})"
end
instance : ToString LValue where toString := LValue.toString
instance : ToString (Typed LValue) where toString := LValue.typedToString

instance : ToString (Typed Symbol) where
  toString ts := s!"({ts.data} : {ts.typ})"

mutual
def Stmt.toString (s : Stmt) : String :=
  match s with
  | .decl name init body =>
    let initStr :=
      match init with
      | none => ""
      | some i => s!", {i}"
    s!"declare({name}{initStr}, {Stmt.listToString body}\n\t)"
  | .assign lv op v => s!"{lv} {op} {v}"
  | .ite cond tt ff =>
    s!"if({cond})\n{Stmt.listToString tt}\n{Stmt.listToString ff}"
  | .while cond body => s!"while({cond})\n{Stmt.listToString body}"
  | .«return» e => s!"return {e}"
  | .assert e => s!"assert({e})"
  | .expr e => s!"{e}"

def Stmt.listToString (stmts : List Stmt) : String :=
  match stmts with
  | [] => ""
  | stmt :: stmts =>
    s!"\n\t{Stmt.toString stmt};" |>.append (Stmt.listToString stmts)
end

instance : ToString Stmt        where toString := Stmt.toString
instance : ToString (List Stmt) where toString := Stmt.listToString


instance : ToString SDef where toString s := s!"struct {s.name} {s.fields};"

instance : ToString FDecl where toString f := s!"{f.ret} {f.name}({f.params})"
instance : ToString FDef where
  toString f := s!"{f.type} {f.name}({f.params}) {f.body}"

def GDecl.toString : GDecl → String
  | .fdecl f => s!"{f}"
  | .fdef  f => s!"{f}"
  | .sdef  s => s!"{s}"
instance : ToString GDecl where toString := GDecl.toString

instance : ToString Prog where
  toString prog := String.intercalate "\n\n" (prog.map GDecl.toString)
