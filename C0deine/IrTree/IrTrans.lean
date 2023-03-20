
import C0deine.IrTree.IrTree
import C0deine.Type.Tst
import C0deine.Type.Typ
import C0deine.Utils.Symbol
import C0deine.Utils.Comparison
import C0deine.Utils.Context
import C0deine.Utils.Temp
import C0deine.Utils.Label


namespace C0deine.IrTrans

open IrTree

structure StructInfo where
  size : Nat
  alignment : Nat
  fields : Symbol.Map Nat

namespace Env

structure Prog.State : Type where
  vars : Symbol.Map Temp
  functions : Symbol.Map Label
  structs : Symbol.Map StructInfo
  blocks : Label.Map Block         -- finished blocks


def Prog.State.new : Env.Prog.State where
  vars := Std.HashMap.empty
  functions := Std.HashMap.empty
  structs := Std.HashMap.empty
  blocks := Std.HashMap.empty

def Prog := StateT Env.Prog.State Context
instance : Monad Env.Prog := show Monad (StateT _ _) from inferInstance


structure Func.State extends Env.Prog.State where
  curBlockLabel : Label
  curBlockType : BlockType

def Func.State.new (label : Label) : Func.State :=
  { Prog.State.new with curBlockLabel := label, curBlockType := .funcEntry }

def Func := StateT Func.State Context
instance : Monad Func := show Monad (StateT _ _) from inferInstance

def Func.var (v : Symbol) : Env.Func Temp :=
  fun env =>
    match env.vars.find? v with
    | some t => return (t, env)
    | none => do
      let t ← Temp.fresh
      let env' := {env with vars := env.vars.insert v t}
      return (t, env')

def Func.func (f : Symbol) : Env.Func Label :=
  fun env =>
    match env.functions.find? f with
    | some l => return (l, env)
    | none => do
      let l ← Label.fresh
      let env' := {env with functions := env.functions.insert f l}
      return (l, env')

def Func.freshTemp : Env.Func Temp :=
  fun env => return (← Temp.fresh, env)
def Func.freshLabel : Env.Func Label :=
  fun env => return (← Label.fresh, env)

def Func.curBlockLabel : Env.Func Label :=
  fun env => return (env.curBlockLabel, env)
def Func.curBlockType : Env.Func BlockType :=
  fun env => return (env.curBlockType, env)

def Func.addBlock (block : Block)
                  (nextBlock : Label)
                  (nextType : BlockType)
                  : Env.Func Unit :=
  fun env =>
    let blocks := env.blocks.insert block.label block
    return ((), { env with blocks := blocks,
                           curBlockLabel := nextBlock,
                           curBlockType := nextType
                })

end Env

namespace MkTyped

def int (e : IrTree.Expr) : IrTree.TypedExpr := .typed (.type (.prim .int)) e
def bool (e : IrTree.Expr) : IrTree.TypedExpr := .typed (.type (.prim .bool)) e
def null (e : IrTree.Expr) : IrTree.TypedExpr := .typed .any e

def expr (env : Env.Func ((List IrTree.Stmt) × IrTree.Expr))
         (typ : Typ.Check)
         : Env.Func ((List IrTree.Stmt) × IrTree.TypedExpr) := do
  let (stmts, e') ← env
  return (stmts, .typed typ e')

end MkTyped

def Trans.binop_op_int (op : Tst.BinOp.Int)
                       : IrTree.PureBinop ⊕ IrTree.EffectBinop :=
  match op with
  | .plus => .inl (.add)
  | .minus => .inl (.sub)
  | .times => .inl (.mul)
  | .div => .inr (.div)
  | .mod => .inr (.mod)
  | .and => .inl (.and)
  | .xor => .inl (.xor)
  | .or => .inl (.or)
  | .lsh => .inr (.lsh)
  | .rsh => .inr (.rsh)

def Trans.binop_op (op : Tst.BinOp)
                   : IrTree.PureBinop ⊕ IrTree.EffectBinop :=
  match op with
  | .int iop => Trans.binop_op_int iop
  | .bool bop => sorry
  | .cmp c => .inl (.comp c)

mutual
partial def Trans.expr
               (exp : Tst.Expr)
               : Env.Func ((List IrTree.Stmt) × IrTree.Expr) := do
  match exp with
  | .num (v : UInt32) => return ([], .const (Int.ofNat v.toNat))
  | .var (name : Symbol) => return ([], .temp (← Env.Func.var name))
  | .«true» => return ([], .byte 1)
  | .«false» => return ([], .byte 0)
  | .null => return ([], .memory 0)
  | .unop op e =>
    let (stmts, e') ← Trans.texpr e
    match op with
    | .int .neg =>
      let c := MkTyped.int (.const 0)
      return (stmts, .binop .sub c e')
    | .int .not => -- ~x ---> x ^ -1
      let c := MkTyped.int (.const (-1))
      return (stmts, .binop .xor e' c)
    | .bool .neg => -- !x ---> x == 0
      let c := MkTyped.int (.const 0)
      return (stmts, .binop (.comp .equal) e' c)

  | .binop op l r =>
    let (stmts1, l') ← Trans.texpr l
    let (stmts2, r') ← Trans.texpr r
    match Trans.binop_op op with
    | .inl op' => return (stmts1.append stmts2, .binop op' l' r') -- pure
    | .inr op' =>
      let dest ← Env.Func.freshTemp
      let effect := .effect dest op' l' r'
      let shift := -- include bounds check
        match op' with
        | .lsh | .rsh => [.check (.shift r')]
        | .div | .mod => []
      return ([stmts1, stmts2, shift, [effect]].join, .temp dest)

  | .ternop cond tt ff =>
    let lT ← Env.Func.freshLabel
    let lF ← Env.Func.freshLabel
    let lN ← Env.Func.freshLabel
    let dest ← Env.Func.freshTemp

    let (stmts, cond') ← Trans.texpr cond
    let exit := .cjump cond' lT lF
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, stmts, exit⟩
    let () ← Env.Func.addBlock block lT .ternaryTrue

    let (stmtsT, tt') ← Trans.texpr tt
    let exitT := .jump lN
    let destT := .move dest tt'
    let blockT := ⟨lT, .ternaryTrue, stmtsT.append [destT], exitT⟩
    let () ← Env.Func.addBlock blockT lF .ternaryFalse

    let (stmtsF, ff') ← Trans.texpr ff
    let exitF := .jump lN
    let destF := .move dest ff'
    let blockF := ⟨lF, .ternaryFalse, stmtsF.append [destF], exitF⟩
    let () ← Env.Func.addBlock blockF lN .afterTernary

    return ([], .temp dest)

  | .app f args =>
    let (stmts, args') ← Trans.args args
    let func_lbl ← Env.Func.func f
    let dest ← Env.Func.freshTemp
    let call := .call dest func_lbl args'
    return (stmts.append [call], .temp dest)

  | .alloc ty => sorry
  | .alloc_array ty e => sorry
  | .dot e field => sorry
  | .deref e => sorry
  | .index e indx => sorry

partial def Trans.texpr (texp : Tst.Typed Tst.Expr)
                  : Env.Func ((List IrTree.Stmt) × IrTree.TypedExpr) :=
  MkTyped.expr (Trans.expr texp.data) texp.typ

partial def Trans.args (args : List (Tst.Typed Tst.Expr))
                : Env.Func ((List IrTree.Stmt) × (List IrTree.TypedExpr)) := do
  match args with
  | [] => return ([], [])
  | arg :: args =>
    let (stmts, arg') ← Trans.texpr arg
    let (stmts', args') ← Trans.args args
    return (stmts.append stmts', arg' :: args')
end
