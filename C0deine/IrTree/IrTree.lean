import Std
import C0deine.Type.Typ
import C0deine.Utils.Temp
import C0deine.Utils.Label
import C0deine.Utils.Comparison

namespace C0deine.IrTree

inductive PureBinop
| add | sub | mul | and | xor | or
| comp : Comparator → PureBinop

inductive EffectBinop
| div | mod | lsh | rsh

mutual
inductive Expr
| byte : UInt8 → Expr
| const : UInt32 → Expr
| temp : Temp → Expr
| memory : Nat → Expr
| binop (op : PureBinop) (lhs rhs : TypedExpr)

inductive TypedExpr
| typed (type : Typ) (expr : Expr)
end

def TypedExpr.type : TypedExpr → Typ
| .typed type _expr => type

def TypedExpr.expr : TypedExpr → Expr
| .typed _type expr => expr

structure Address where
  base : TypedExpr
  offset : Option Int
  index : Option (TypedExpr)
  scale : Nat

inductive Check
| null : TypedExpr → Check
| shift : TypedExpr → Check
| bounds (source index : TypedExpr)

inductive Stmt
| move (dest : Temp) (te : TypedExpr)
| effect (dest : Temp) (op : EffectBinop) (lhs rhs : TypedExpr)
| call (dest : Temp) (name : Label) (args : List (TypedExpr))
| load (dest : Temp) (addr : Address)
| store (addr : Address) (source : TypedExpr)
| check (c : Check)

inductive BlockExit
| jump (lbl : Label)
| cjump (op : PureBinop) (lhs rhs : TypedExpr) (tt : Label) (ff : Label)
| «return» (e : Option (TypedExpr))

structure Block where
  label : Label
  body : List Stmt
  exit : BlockExit

structure Func where
  name : Label
  enter : Label
  args : List Temp
  blocks : List Block

def Prog := List Func

def PureBinop.toString : PureBinop → String
  | add      => "+"
  | sub      => "-"
  | mul      => "*"
  | and      => "&"
  | xor      => "^"
  | or       => "|"
  | comp cmp => s!"{cmp}"
instance : ToString PureBinop where toString := PureBinop.toString

def EffectBinop.toString : EffectBinop → String
  | div => "/"
  | mod => "%"
  | lsh => "<<"
  | rsh => ">>"
instance : ToString EffectBinop where toString := EffectBinop.toString

mutual
def Expr.toString : Expr → String
  | .byte b => s!"{b}"
  | .const c => s!"{c}"
  | .temp t => s!"{t}"
  | .memory m => s!"m{m}"
  | .binop op lhs rhs => s!"{lhs.toString} {op} {rhs.toString}"

def TypedExpr.toString : TypedExpr → String
  | .typed _type expr => expr.toString
end

instance : ToString Expr where toString := Expr.toString
instance : ToString TypedExpr where toString := TypedExpr.toString

def Address.toString (addr : Address) : String :=
  match addr.index with
  | .none => s!"M[{addr.base} + {addr.offset}]"
  | .some idx => s!"M[{addr.base} + {addr.scale} * {idx} + {addr.offset}]"
instance : ToString Address where toString := Address.toString

def Check.toString : Check → String
  | .null e => s!"null_check({e})"
  | .shift e => s!"shift_check({e})"
  | .bounds source index => s!"bounds_check({source}[{index}])"
instance : ToString Check where toString := Check.toString

def Stmt.toString : Stmt → String
  | move dest te => s!"{dest} <-- {te}"
  | effect dest op lhs rhs => s!"{dest} <!- {lhs} {op} {rhs}"
  | call dest name args => s!"{dest} <-- {name}({args})"
  | load dest addr => s!"{dest} <-- M[{addr}]"
  | store addr source => s!"M[{addr}] <-- {source}"
  | check c => s!"{c}"
instance : ToString Stmt where toString := Stmt.toString

def BlockExit.toString : BlockExit → String
  | jump lbl => s!"jump {lbl}"
  | cjump op lhs rhs tt ff =>
    s!"cjump ({lhs} {op} {rhs}) {tt} {ff}"
  | «return» (.none) => "return"
  | «return» (.some e) => s!"return {e}"
instance : ToString BlockExit where toString := BlockExit.toString

def Block.toString (b : Block) :=
  let body := b.body.map (fun stmt => s!"\t{stmt}\n") |> String.join
  s!"{b.label}:\n{body}\t{b.exit}"
instance : ToString Block where toString := Block.toString

def Func.toString (f : Func) :=
  let blocks := f.blocks.map (fun b => s!"{b}\n") |> String.join
  s!"{f.name}: ({f.args})\n\tjump {f.enter}\n{blocks}"
instance : ToString Func where toString := Func.toString

def Prog.toString (prog : Prog) :=
  prog.map (fun f => s!"{f}\n\n") |> String.join
instance : ToString Prog where toString := Prog.toString
