/- C0deine - CST
   Representation for the Concrete Syntax Tree which is what the Parser directly
   parses into. This representation is the closest to the source code.
   - James Gallicchio
   - Thea Brick
 -/
import Numbers
import C0deine.AuxDefs
import C0deine.Context.Symbol

namespace C0deine.Cst

open Numbers

def Ident := Symbol
deriving ToString, Repr

inductive Typ
| int
| bool
| char
| string
| void
| tydef (name : Ident)
| ptr : Typ → Typ
| arr : Typ → Typ
| struct (name : Ident)
deriving Repr, Inhabited

inductive UnOp.Int | neg | not
deriving Repr

inductive UnOp.Bool | not
deriving Repr

inductive UnOp
| int (op : UnOp.Int)
| bool (op : UnOp.Bool)
deriving Repr

inductive BinOp.Int
| plus | minus | times | div | mod | and | xor | or | lsh | rsh
deriving Repr

inductive BinOp.Cmp
| lt | le | gt | ge | eq | ne
deriving Repr

inductive BinOp.Bool
| and | or
deriving Repr

inductive BinOp
| int (op : BinOp.Int)
| cmp (op : BinOp.Cmp)
| bool (op : BinOp.Bool)
deriving Repr

inductive AsnOp
| eq | aseq (op : BinOp.Int)
deriving Repr

inductive PostOp
| incr | decr
deriving Repr

inductive Expr
| num  (v : Int32)
| char (c : Char)
| str  (s : String)
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
| result
| length (e : Expr)
deriving Repr, Inhabited

inductive LValue
| var (name : Ident)
| dot (lv : LValue) (field : Ident)
| arrow (lv : LValue) (field : Ident)
| deref (lv : LValue)
| index (lv : LValue) (index : Expr)

def LValue.toExpr : LValue → Expr
| .var name => .var name
| .dot lv field => .dot lv.toExpr field
| .arrow lv field => .arrow lv.toExpr field
| .deref lv => .deref lv.toExpr
| .index lv idx => .index lv.toExpr idx

inductive Spec
| requires   : Expr → Spec
| ensures    : Expr → Spec
| loop_invar : Expr → Spec
| assert     : Expr → Spec

inductive Anno
| line  : List Spec → Anno
| block : List Spec → Anno

mutual
inductive Control
| ite (cond : Expr) (tt : Stmt) (ff : Stmt)
| while (cond : Expr) (body : Stmt)
| «for» (init : Option Simp) (cond : Expr) (step : Option Simp) (body : Stmt)
| «return» (e : Option Expr)
| assert (e : Expr)
| error (e : Expr)

inductive Simp
| assn (lv : LValue) (op : AsnOp) (v : Expr)
| post (lv : LValue) (op : PostOp)
| decl (type : Typ) (name : Ident) (init : Option Expr)
| exp (e : Expr)

inductive Stmt
| simp  : Simp → Stmt
| ctrl  : Control → Stmt
| block : List Stmt → List Anno → Stmt
| anno  : Anno → Stmt → Stmt
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

structure FDecl where
  type : Typ
  name : Ident
  params : List Param
  annos : List Anno

structure FDef extends FDecl where
  body : Stmt

inductive Directive
| use_lib : String → Directive
| use_str : String → Directive
| unknown : Directive

inductive GDecl
| fdecl : FDecl → GDecl
| fdef  : FDef  → GDecl
| tydef : TyDef → GDecl
| sdecl : SDecl → GDecl
| sdef  : SDef  → GDecl
| cdir  : Directive → GDecl

def Prog := List GDecl
deriving Inhabited
instance : HAppend Prog Prog Prog := ⟨List.append⟩

-- directives must appear at the start of file so this removes them
def splitDirectives : Prog → List Directive × Prog
  | [] => ([], [])
  | (.cdir d) :: rest =>
    let (dirs, prog) := splitDirectives rest
    (d::dirs, prog)
  | prog => ([], prog)

def Typ.toString : Typ → String
  | .int => "int"
  | .bool => "bool"
  | .char => "char"
  | .string => "string"
  | .void => "'void"
  | .tydef (name : Ident) => s!"alias {name}"
  | .ptr ty => s!"{ty.toString}*"
  | .arr ty => s!"{ty.toString}[]"
  | .struct (name : Ident) => s!"struct {name}"
instance : ToString Typ where toString := Typ.toString


def UnOp.Int.toString : UnOp.Int → String
  | .neg => "~"
  | .not => "!"
instance : ToString UnOp.Int where toString := UnOp.Int.toString

def UnOp.Bool.toString : UnOp.Bool → String
  | .not => "!"
instance : ToString UnOp.Bool where toString := UnOp.Bool.toString

def UnOp.toString : UnOp → String
  | .int op  => s!"{op}"
  | .bool op => s!"{op}"
instance : ToString UnOp where toString := UnOp.toString


def BinOp.Int.toString : BinOp.Int → String
  | .plus => "+"
  | .minus => "-"
  | .times => "*"
  | .div => "/"
  | .mod => "%"
  | .and => "&"
  | .xor => "^"
  | .or => "|"
  | .lsh => "<<"
  | .rsh => ">>"
instance : ToString BinOp.Int where toString := BinOp.Int.toString

def BinOp.Cmp.toString : BinOp.Cmp → String
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="
  | .eq => "=="
  | .ne => "!="
instance : ToString BinOp.Cmp where toString := BinOp.Cmp.toString

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

def PostOp.toString : PostOp → String
  | incr => "++"
  | decr => "--"
instance : ToString PostOp where toString := PostOp.toString


mutual
partial def Expr.toString : Expr → String
  | .num v  => s!"{v}"
  | .char c => s!"'{c.toString.sanitise}'"
  | .str s  => s!"\"{s.sanitise}\""
  | .true   => "true"
  | .false  => "false"
  | .null   => "NULL"
  | .unop op e => s!"{op}({e.toString})"
  | .binop op l r => s!"({l.toString}) {op} ({r.toString})"
  | .ternop c tt ff => s!"({c.toString}) ? ({tt.toString}) : ({ff.toString})"
  | .app f args => s!"{f}({Expr.argsToString args})"
  | .alloc ty => s!"alloc({ty})"
  | .alloc_array ty e => s!"alloc_array({ty}, {e.toString})"
  | .var name => s!"{name}"
  | .dot e field => s!"({e.toString}).{field}"
  | .arrow e field => s!"({e.toString})->{field}"
  | .deref e => s!"*({e.toString})"
  | .index e i => s!"({e.toString})[{i.toString}]"
  | .result => "\\result"
  | .length e => s!"\\length({e.toString})"

partial def Expr.argsToString : List Expr → String
  | [] => ""
  | arg :: [] => s!"{arg.toString}"
  | arg :: args => s!"{arg.toString}, {Expr.argsToString args}"
end
instance : ToString Expr where toString := Expr.toString


def LValue.toString : LValue → String
  | .var name      => s!"{name}"
  | .dot e field   => s!"({e.toString}).{field}"
  | .arrow e field => s!"({e.toString})->{field}"
  | .deref e       => s!"*({e.toString})"
  | .index e i     => s!"({e.toString})[{i.toString}]"
instance : ToString LValue where toString := LValue.toString

def Spec.toString : Spec → String
  | .requires e   => s!"requires {e.toString};"
  | .ensures e    => s!"ensures {e.toString};"
  | .loop_invar e => s!"loop_invariant {e.toString};"
  | .assert e     => s!"assert {e.toString};"
instance : ToString Spec := ⟨Spec.toString⟩

def Anno.toString : Anno → String
  | .line s  => s!"//@ {String.intercalate " " (s.map Spec.toString)}\n"
  | .block s => s!"/*@ {String.intercalate " " (s.map Spec.toString)} @*/"
instance : ToString Anno := ⟨Anno.toString⟩

mutual
partial def Stmt.toString (s : Stmt) : String :=
  match s with
  | .simp s    => Simp.toString s
  | .ctrl c    => Control.toString c
  | .block b a =>
    let sb := Stmt.listToString b |>.replace "\n" "\n  "
    let sa := String.intercalate "\n  " (a.map Anno.toString)
    "{\n  " ++ sb ++ "\n  " ++ sa ++ "\n}"
  | .anno a s  => Anno.toString a ++ "\n" ++ Stmt.toString s

partial def Stmt.listToString (stmts : List Stmt) : String :=
  match stmts with
  | []            => ""
  | stmt::[]      => Stmt.toString stmt
  | stmt :: stmts => s!"{Stmt.toString stmt}\n{Stmt.listToString stmts}"

partial def Control.toString (c : Control) : String :=
  match c with
  | .ite cond tt ff =>
    let stt := Stmt.toString tt |>.replace "\n" "\n  "
    let sff := Stmt.toString ff |>.replace "\n" "\n  "
    s!"if({cond})\n  {stt}\n  {sff}\n"
  | .while cond body =>
    let sbody := Stmt.toString body |>.replace "\n" "\n  "
    s!"while({cond})\n  {sbody}\n"
  | .«for» init cond step body =>
    let initStr :=
      match init with
      | none => ""
      | some i => Simp.toString i
    let stepStr :=
      match step with
      | none => ""
      | some s => Simp.toString s
    let sbody := Stmt.toString body |>.replace "\n" "\n  "
    s!"for({initStr}; {cond}; {stepStr})\n  {sbody}\n"
  | .«return» (.none) => "return;"
  | .«return» (.some e) => s!"return {e};"
  | .assert e => s!"assert({e});"
  | .error e  => s!"error({e});"

partial def Simp.toString (s : Simp) : String :=
  match s with
  | .assn lv op v => s!"{lv} {op} {v}"
  | .post lv op => s!"({lv}){op}"
  | .decl type name init =>
    let initStr :=
      match init with
      | none => ""
      | some i => s!" = {i}"
    s!"{type} {name} {initStr};"
  | .exp e => s!"{e};"
end
instance : ToString Stmt        where toString := Stmt.toString
instance : ToString (List Stmt) where toString := Stmt.listToString
instance : ToString Control     where toString := Control.toString
instance : ToString Simp        where toString := Simp.toString


instance : ToString Field where toString f := s!"{f.type} {f.name};"
instance : ToString (List Field) where
  toString fs := "{".append (fs.foldr (fun f acc => s!"\t{f}\n{acc}") "}")

instance : ToString SDef where toString s := s!"struct {s.name} {s.fields};"
instance : ToString SDecl where toString s := s!"struct {s.name};"

instance : ToString TyDef where toString t := s!"typedef {t.type} {t.name};"

instance : ToString Param where toString p := s!"{p.type} {p.name}"
instance : ToString (List Param) where
  toString ps := String.intercalate ", " (ps.map (fun p => s!"{p}"))

instance : ToString FDecl where toString f :=
  let sa := String.intercalate "\n  " (f.annos.map Anno.toString)
  s!"{f.type} {f.name}({f.params})\n  {sa}"
instance : ToString FDef where
  toString f := s!"{f.type} {f.name}({f.params}) {f.body}"

def Directive.toString : Directive → String
  | .use_lib s => s!"#use <{s}>"
  | .use_str s => s!"#use \"{s}\""
  | .unknown   => s!"#unknown compiler directive!"
instance : ToString Directive := ⟨Directive.toString⟩

def GDecl.toString : GDecl → String
  | .fdecl f => s!"{f}"
  | .fdef  f => s!"{f}"
  | .tydef t => s!"{t}"
  | .sdecl s => s!"{s}"
  | .sdef  s => s!"{s}"
  | .cdir  d => s!"{d}"
instance : ToString GDecl where toString := GDecl.toString

instance : ToString Prog where
  toString prog := String.intercalate "\n\n" (prog.map GDecl.toString)
