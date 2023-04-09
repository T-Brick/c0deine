import Std
import C0deine.Type.Typ
import C0deine.Context.Temp
import C0deine.Context.Label
import C0deine.Utils.Comparison
import C0deine.Utils.ValueSize

namespace C0deine.IrTree

inductive PureBinop
| add | sub | mul | and | xor | or
| comp : Comparator → PureBinop

inductive EffectBinop
| div | mod | lsh | rsh

mutual
inductive Expr
| byte : UInt8 → Expr
| const : Int → Expr
| temp : SizedTemp → Expr
| memory : Nat → Expr
| binop (op : PureBinop) (lhs rhs : TypedExpr)
deriving Inhabited

inductive TypedExpr
| typed (type : Typ) (expr : Expr)
deriving Inhabited
end

def TypedExpr.type : TypedExpr → Typ
  | .typed type _expr => type

def TypedExpr.expr : TypedExpr → Expr
  | .typed _type expr => expr

structure Address where
  base   : TypedExpr
  offset : UInt64
  index  : Option (TypedExpr)
  scale  : Nat
deriving Inhabited

inductive Check
| null : TypedExpr → Check
| shift : TypedExpr → Check
| bounds (source index : TypedExpr)

inductive Stmt
| move (dest : SizedTemp) (te : TypedExpr)
| effect (dest : SizedTemp) (op : EffectBinop) (lhs rhs : TypedExpr)
| call (dest : SizedTemp) (name : Label) (args : List (TypedExpr))
| alloc (dest : Temp) (size : TypedExpr)
| load (dest : SizedTemp) (addr : Address)
| store (addr : Address) (source : TypedExpr)
| check (c : Check)

inductive BlockExit
| jump (lbl : Label)
    -- hotpath = some true => tt will be most likely jump
| cjump (e : TypedExpr) (hotpath : Option Bool) (tt : Label) (ff : Label)
| «return» (e : Option (TypedExpr))

inductive BlockType
| unknown
| loop
| loopguard
| funcEntry
| funcExit
| thenClause
| elseClause
| ternaryTrue
| ternaryFalse
| afterLoop
| afterITE
| afterTernary
| afterRet

structure Block where
  label : Label
  type : BlockType
  body : List Stmt
  exit : BlockExit

structure Func where
  name : Label
  enter : Label
  args : List SizedTemp
  blocks : Label.Map Block

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
  | alloc dest size => s!"{dest} <-- alloc({size})"
  | load dest addr => s!"{dest} <-- M[{addr}]"
  | store addr source => s!"M[{addr}] <-- {source}"
  | check c => s!"{c}"
instance : ToString Stmt where toString := Stmt.toString

def BlockExit.toString : BlockExit → String
  | jump lbl => s!"jump {lbl}"
  | cjump e none tt ff =>
    s!"cjump ({e}) {tt} {ff}"
  | cjump e (some true) tt ff =>
    s!"cjump ({e}) [{tt}] {ff}"
  | cjump e (some false) tt ff =>
    s!"cjump ({e}) {tt} [{ff}]"
  | «return» (.none) => "return"
  | «return» (.some e) => s!"return {e}"
instance : ToString BlockExit where toString := BlockExit.toString

def BlockType.toString : BlockType → String
  | unknown => "unknown"
  | loop => "loop"
  | loopguard => "loop-guard"
  | funcEntry => "func-entry"
  | funcExit => "func-exit"
  | thenClause => "then-clause"
  | elseClause => "else-clause"
  | ternaryTrue => "ternary-true"
  | ternaryFalse => "ternary-false"
  | afterLoop => "after-loop"
  | afterITE => "after-ifelse"
  | afterTernary => "after-ternary"
  | afterRet => "after-return"
instance : ToString BlockType where toString := BlockType.toString

def Block.toString (b : Block) :=
  let body := b.body.map (fun stmt => s!"\t{stmt}\n") |> String.join
  s!"{b.label}:\t\t{b.type}\n{body}\t{b.exit}"
instance : ToString Block where toString := Block.toString

def Func.toString (f : Func) :=
  let blocks := f.blocks.toList.map (fun b => s!"{b.2}\n") |> String.join
  s!"{f.name}: ({f.args})\n\tjump {f.enter}\n{blocks}"
instance : ToString Func where toString := Func.toString

def Prog.toString (prog : Prog) :=
  prog.map (fun f => s!"{f}\n\n") |> String.join
instance : ToString Prog where toString := Prog.toString
