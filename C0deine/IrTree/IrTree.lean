import Std
import C0deine.Type.Typ
import C0deine.Context.Temp
import C0deine.Context.Label
import C0deine.Utils.Comparison
import C0deine.Utils.ValueSize
import C0deine.ControlFlow.CFG

namespace C0deine.IrTree

open Typ

inductive PureBinop
| add | sub | mul | and | xor | or
| comp : Comparator → PureBinop

inductive EffectBinop
| div | mod | lsh | rsh

inductive Expr
| byte : UInt8 → Expr
| const : Int → Expr
| temp : SizedTemp → Expr
| memory : Nat → Expr
| binop (op : PureBinop) (lhs rhs : Typed Expr)
| and (lhs rhs : Typed Expr)
| or (lhs rhs : Typed Expr)
deriving Inhabited

structure Address where
  base   : Typed Expr
  offset : UInt64
  index  : Option (Typed Expr)
  scale  : Nat
deriving Inhabited

inductive Check
| null : Typed Expr → Check
| shift : Typed Expr → Check
| bounds (source index : Typed Expr)

inductive Stmt
| move (dest : SizedTemp) (te : Typed Expr)
| effect (dest : SizedTemp) (op : EffectBinop) (lhs rhs : Typed Expr)
| call (dest : SizedTemp) (name : Label) (args : List (Typed Expr))
| alloc (dest : Temp) (size : Typed Expr)
| load (dest : SizedTemp) (addr : Address)
| store (addr : Address) (source : Typed Expr)
| check (c : Check)

inductive BlockExit
| jump (lbl : Label)
    -- hotpath = some true => tt will be most likely jump
| cjump (e : Typed Expr) (hotpath : Option Bool) (tt : Label) (ff : Label)
| «return» (e : Option (Typed Expr))
instance : Inhabited BlockExit := ⟨.return .none⟩

def Block := ControlFlow.Block Stmt BlockExit

structure Func where
  name : Label
  enter : Label
  args : List SizedTemp
  blocks : Label.Map Block
  enter_in : blocks.contains enter

def Block.succ_labels (f : Func) (b : Block) : Option (List Label) :=
  f.blocks.find? b.label |>.map (fun b => (
      match b.exit with
      | .jump lbl => [lbl]
      | .cjump _ (.some false) tt ff => [ff, tt]
      | .cjump _ _ tt ff => [tt, ff]
      | .«return» _      => []
    )
  )

def Block.succ (f : Func) (b : Block) : Option (List Block) :=
  b.succ_labels f |>.map (List.filterMap f.blocks.find?)

def Func.to_cfg (f : Func) : ControlFlow.C0_CFG Stmt BlockExit :=
  let labels := (f.blocks.toList).map (·.fst)
  let succ := fun l =>
    if f.blocks.contains l then
      match f.blocks.find? l |>.bind (Block.succ_labels f) with
      | .none => []
      | .some lbls => lbls
    else []
  let graph := ControlFlow.Digraph.of_succ labels succ
  let cfg := ControlFlow.CFG.mk graph ⟨f.enter, sorry⟩ sorry
  ⟨cfg, f.name, f.blocks⟩

@[inline] def _root_.C0deine.Label.loop (f : Func) (l : Label) : Bool :=
  match f.blocks.find? l with
  | .some b => b.loop
  | _       => false

@[inline] def _root_.C0deine.Label.after_loop (f : Func) (l : Label) : Bool :=
  match f.blocks.find? l with
  | .some b => b.after_loop
  | _       => false

def Prog := List Func

def Prog.to_cfgs (prog : Prog) := prog.map (Func.to_cfg ·)

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

partial def Expr.toString : Expr → String
  | .byte b => s!"{b}"
  | .const c => s!"{c}"
  | .temp t => s!"{t}"
  | .memory m => s!"&{m}"
  | .binop op lhs rhs => s!"{lhs.data.toString} {op} {rhs.data.toString}"
  | .and lhs rhs => s!"{lhs.data.toString} && {rhs.data.toString}"
  | .or lhs rhs => s!"{lhs.data.toString} || {rhs.data.toString}"

instance : ToString Expr where toString := Expr.toString
instance : ToString (Typed Expr) where toString texpr := texpr.data.toString

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
  | load dest addr => s!"{dest} <-- {addr}"
  | store addr source => s!"{addr} <-- {source}"
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
