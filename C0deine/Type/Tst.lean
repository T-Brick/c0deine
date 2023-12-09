/-
  A Typed Syntax Tree, which is similar to the AST, but with expressions
  having typed annotations. Types are dealiased in this representation.
 -/
import Numbers
import C0deine.Type.Typ
import C0deine.Context.Symbol
import C0deine.Utils.Comparison

namespace C0deine.Tst

open Typ

inductive UnOp.Int  | neg | not deriving Inhabited
inductive UnOp.Bool | neg       deriving Inhabited
inductive UnOp
| int (op : UnOp.Int)
| bool (op : UnOp.Bool)
deriving Inhabited

inductive BinOp.Int
| plus | minus | times | div | mod | and | xor | or | lsh | rsh
deriving Inhabited

inductive BinOp.Bool
| and | or
deriving Inhabited

inductive BinOp
| int (op : BinOp.Int)
| cmp (op : Comparator)
| bool (op : BinOp.Bool)
deriving Inhabited

inductive Expr
| num (v : Int32)
| char (c : Char)
| str (s : String)
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
| result
| length (e : Typed Expr)
deriving Inhabited

inductive Expr.All (P : Expr → Bool) : Expr → Prop
| num     : P (.num  v) → All P (.num  v)
| char    : P (.char c) → All P (.char c)
| str     : P (.str  s) → All P (.str  s)
| var     : P (.var  x) → All P (.var  x)
| «true»  : P (.true  ) → All P (.true  )
| «false» : P (.false ) → All P (.false )
| null    : P (.null  ) → All P (.null  )
| unop
  : All P te.data
  → P (.unop op te)
  → All P (.unop op te)
| binop
  : All P tl.data
  → All P tr.data
  → P (.binop op tl tr)
  → All P (.binop op tl tr)
| ternop
  : All P cc.data
  → All P tt.data
  → All P ff.data
  → P (.ternop cc tt ff)
  → All P (.ternop cc tt ff)
| app
  : (∀ a ∈ args, All P a.data)
  → P (.app f args)
  → All P (.app f args)
| alloc : P (.alloc ty) → All P (.alloc ty)
| alloc_array
  : All P te.data
  → P (.alloc_array ty te)
  → All P (.alloc_array ty te)
| dot
  : All P te.data
  → P (.dot te f)
  → All P (.dot te f)
| deref
  : All P te.data
  → P (.deref te)
  → All P (.deref te)
| index
  : All P te.data
  → All P indx.data
  → P (.index te indx)
  → All P (.index te indx)
| result
  : P .result
  → All P (.result)
| length
  : All P te.data
  → P (.length te)
  → All P (.length te)

@[inline] def Expr.OnlyContract : Expr → Bool
  | .result   => .true
  | .length _ => .true
  | _         => .false
@[inline] def Expr.IsResult : Expr → Bool
  | .result => .true
  | _       => .false

@[inline] def Expr.no_contract : Expr → Bool := .not ∘ Tst.Expr.OnlyContract
@[inline] def Expr.no_result   : Expr → Bool := .not ∘ Tst.Expr.IsResult
abbrev Expr.NoContract := {e : Expr // Expr.All no_contract e}
abbrev Expr.NoResult   := {e : Expr // Expr.All no_result   e}

inductive LValue
| var (name : Symbol)
| dot (lv : Typed LValue) (field : Symbol)
| deref (lv : Typed LValue)
| index (lv : Typed LValue) (index : Typed Expr.NoContract)
deriving Inhabited

inductive Anno
| requires   : Typed Expr.NoResult → Anno
| ensures    : Typed Expr          → Anno
| loop_invar : Typed Expr.NoResult → Anno
| assert     : Typed Expr.NoResult → Anno

-- only requires/ensures can annotate functions
@[inline, reducible] def Anno.function : Anno → Bool
  | .requires _   => true
  | .ensures _    => true
  | .loop_invar _ => false
  | .assert _     => false

-- only loop_invariant and assert can annotate loops
@[inline, reducible] def Anno.loop : Anno → Bool
  | .requires _   => false
  | .ensures _    => false
  | .loop_invar _ => true
  | .assert _     => false

-- only assert can be not attatched to a loop/function
@[inline, reducible] def Anno.free : Anno → Bool
  | .requires _   => false
  | .ensures _    => false
  | .loop_invar _ => false
  | .assert _     => true

abbrev Anno.Loop     := {a : Anno // Anno.loop     a}
abbrev Anno.Function := {a : Anno // Anno.function a}
abbrev Anno.Free     := {a : Anno // Anno.free     a}

inductive Stmt
| decl (name : Typed Symbol) (init : Option (Typed Expr.NoContract)) (body : List Stmt)
| assign (lhs : Typed LValue) (op : Option BinOp.Int) (rhs : Typed Expr.NoContract)
| expr (e : Typed Expr.NoContract)
| ite (cond : Typed Expr.NoContract) (tt : List Stmt) (ff : List Stmt)
| while (cond : Typed Expr.NoContract) (annos : List Anno.Loop) (body : List Stmt)
| «return» (e : Option (Typed Expr.NoContract))
| assert (e : Typed Expr.NoContract)
| error (e : Typed Expr.NoContract)
| anno (a : Anno.Free)
deriving Inhabited

structure SDef where
  name : Symbol
  fields : List (Typed Symbol)

structure FDef where
  type : Option Typ
  name : Symbol
  params : List (Typed Symbol)
  annos : List Anno.Function
  body : List Stmt

structure FDecl where
  ret : Option Typ
  name : Symbol
  params : List Typ
  annos : List Anno

inductive GDecl
| fdecl : FDecl → GDecl
| fdef  : FDef  → GDecl
| sdef  : SDef  → GDecl

/- Functions calls that a program makes
    True means the call is used in a contract, so the function must be pure.
-/
def Calls := Symbol.Map Bool

def Calls.merge (calls1 calls2 : Calls) : Calls :=
  calls1.mergeWith (fun _ x y => x || y) calls2

structure Prog where
  header  : List GDecl
  body    : List GDecl
  calls   : Calls
  strings : List String


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
partial def Expr.toString : Expr → String
  | .num v => s!"{v}"
  | .char c => s!"'{c}'"
  | .str s => s!"\"{s}\""
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
  | .result => "\\result"
  | .length e => s!"\\length {Expr.typedToString e}"

partial def Expr.argsToString : List (Typed Expr) → String
  | [] => ""
  | arg :: [] => s!"{Expr.typedToString arg}"
  | arg :: args => s!"{Expr.typedToString arg}, {Expr.argsToString args}"

partial def Expr.typedToString (texpr : Typed Expr) : String :=
  @Typed.toString Expr ⟨Expr.toString⟩ texpr
end

instance : ToString Expr := ⟨Expr.toString⟩
instance : ToString (List (Typed Expr)) where
  toString texps := texps.map Expr.typedToString |> String.intercalate ", "

def Anno.toString : Anno → String
  | .requires e   => s!"//@requires {e}"
  | .ensures e    => s!"//@ensures {e}"
  | .loop_invar e => s!"//@loop_invariant {e}"
  | .assert e     => s!"//@assert {e}"
instance : ToString Anno := ⟨Anno.toString⟩
def Anno.listToString : List Anno → String
  | [] => ""
  | as => String.intercalate "\n  " (as.map Anno.toString) ++ "\n  "
instance : ToString (List Anno) := ⟨Anno.listToString⟩

mutual
partial def LValue.toString : LValue → String
  | var name => s!"{name}"
  | dot e field =>
    s!"({LValue.typedToString e}).{field}"
  | deref e => s!"*({LValue.typedToString e})"
  | index e i => s!"({LValue.typedToString e})[{i}]"
where LValue.typedToString (tlv : Typed LValue) : String :=
  @Typed.toString LValue ⟨LValue.toString⟩ tlv
end

instance : ToString LValue where toString := LValue.toString
instance : ToString (List (Typed Symbol)) where
  toString tss := tss.map Typed.toString |> String.intercalate ", "

mutual
partial def Stmt.toString (s : Stmt) : String :=
  match s with
  | .decl name init body =>
    let initStr :=
      match init with
      | none => ""
      | some i => s!", {i}"
    let str_body := (Stmt.listToString body).replace "\n" "\n  "
    s!"declare({name}{initStr},\n  {str_body}\n)"
  | .assign lv (.none) v => s!"{lv} = {v}"
  | .assign lv (.some op) v => s!"{lv} {op}= {v}"
  | .ite cond tt ff =>
    let str_tt := (Stmt.listToString tt).replace "\n" "\n  "
    let str_ff := (Stmt.listToString ff).replace "\n" "\n  "
    s!"if{cond}\n  {str_tt}\nelse\n  {str_ff}\nendif"
  | .while cond annos body =>
    let str_annos := Anno.listToString annos
    let str_body := (Stmt.listToString body).replace "\n" "\n  "
    s!"while{cond}\n  {str_annos}{str_body}\nendwhile"
  | .«return» .none => s!"return"
  | .«return» (.some e) => s!"return {e}"
  | .assert e => s!"assert{e}"
  | .error e => s!"error{e}"
  | .expr e => s!"{e}"
  | .anno a => Anno.toString a

partial def Stmt.listToString (stmts : List Stmt) : String :=
  match stmts with
  | [] => "nop;"
  | [stmt] => s!"{Stmt.toString stmt};"
  | stmt :: stmts =>
    s!"{Stmt.toString stmt};\n{Stmt.listToString stmts}"
end

instance : ToString Stmt        where toString := Stmt.toString
instance : ToString (List Stmt) where toString := Stmt.listToString


instance : ToString SDef where
  toString s :=
    s!"struct {s.name}".append ("{".append ( s!"{s.fields}".append "};"))

instance : ToString FDecl where toString f :=
  s!"{f.ret} {f.name}({f.params})\n  {Anno.listToString f.annos}"
instance : ToString FDef where
  toString f :=
    let str_anno := Anno.listToString f.annos
    let str_body := (toString f.body).replace "\n" "\n  "
    s!"{f.type} {f.name}({f.params})\n  {str_anno}{str_body}\nend {f.name}"

def GDecl.toString : GDecl → String
  | .fdecl f => s!"{f}"
  | .fdef  f => s!"{f}"
  | .sdef  s => s!"{s}"
instance : ToString GDecl where toString := GDecl.toString

instance : ToString Prog where
  toString prog :=
    let calls_str  := prog.calls.toList.map (fun (f, pure) =>
        if pure then s!"{f} (pure)" else s!"{f}")
      |> String.intercalate "\n  "
    let string_str := prog.strings.map (·.replace "\n" "\n    ")
      |> String.intercalate "\n  - "
    let prog_str := prog.header
      |>.append prog.body
      |>.map GDecl.toString
      |> String.intercalate "\n\n"
    s!"-----  Calls  -----\n  {calls_str}\n
----- Strings -----\n  - {string_str}\n
----- Program -----\n\n{prog_str}\n
----- ------- -----\n"
