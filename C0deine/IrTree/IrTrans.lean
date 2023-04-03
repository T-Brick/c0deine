
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
  size : UInt64
  alignment : UInt64
  fields : Symbol.Map UInt64
instance : Inhabited StructInfo where default := ⟨0, 0, Std.HashMap.empty⟩

namespace Env

structure Prog.State : Type where
  isUnsafe : Bool
  vars : Symbol.Map Temp
  functions : Symbol.Map Label
  structs : Symbol.Map StructInfo
  blocks : Label.Map Block         -- finished blocks


def Prog.State.new : Env.Prog.State where
  isUnsafe := false
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
instance [Inhabited α] : Inhabited (Func α) :=
  show Inhabited (StateT _ _ α) from inferInstance
instance : Monad Func := show Monad (StateT _ _) from inferInstance

def Func.unsafe : Env.Func Bool :=
  fun env => return ⟨env.isUnsafe, env⟩

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

def Func.structs : Env.Func (Symbol.Map StructInfo) :=
  fun env => return ⟨env.structs, env⟩

end Env

namespace MkTyped

def int (e : IrTree.Expr) : IrTree.TypedExpr := .typed (.prim .int) e
def bool (e : IrTree.Expr) : IrTree.TypedExpr := .typed (.prim .bool) e
def null (e : IrTree.Expr) : IrTree.TypedExpr := .typed .any e

def expr (env : Env.Func ((List IrTree.Stmt) × IrTree.Expr))
         (typ : Typ)
         : Env.Func ((List IrTree.Stmt) × IrTree.TypedExpr) := do
  let (stmts, e') ← env
  return (stmts, .typed typ e')

end MkTyped

def Typ.size (tau : Typ) : Env.Func (Option UInt64) := do
  match tau with
  | .any => return none
  | .prim .int  => return some 4
  | .prim .bool => return some 4
  | .mem (.pointer _) => return some 8
  | .mem (.array _)   => return some 8
  | .mem (.struct n)  =>
    let s ← Env.Func.structs
    return s.find? n |>.map (fun info => info.size)

namespace Trans

def binop_op_int (op : Tst.BinOp.Int)
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

def binop_op (op : Tst.BinOp)
             : IrTree.PureBinop ⊕ IrTree.EffectBinop :=
  match op with
  | .int iop => Trans.binop_op_int iop
  | .bool bop => sorry
  | .cmp c => .inl (.comp c)

mutual
partial def expr (tau : Typ)
         (exp : Tst.Expr)
         : Env.Func ((List IrTree.Stmt) × IrTree.Expr) := do
  match exp with
  | .num (v : Int32) => return ([], .const v)
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

  | .alloc ty =>
    match ← Typ.size ty with
    | some size =>
      let dest ← Env.Func.freshTemp
      return ([.alloc dest (MkTyped.int (.memory size.toNat))], .temp dest)
    | none => panic! "IR Trans: Alloc type size not known"

  | .alloc_array ty e =>
    match ← Typ.size ty with
    | some size =>
      let (stmts, e') ← Trans.texpr e
      let dest ← Env.Func.freshTemp
      if ← Env.Func.unsafe
      then
        let size' := -- don't need to store length if unsafe
          match e' with -- optimise if size is constant
          | .typed _tau (.const c) =>
            match c.toNat' with
            | some n => .memory (n * size.toNat)
            | none   => .binop .mul e' (MkTyped.int (.const size.toNat))
          | .typed _tau _len => .binop .mul e' (MkTyped.int (.const size.toNat))
        return (stmts.append [.alloc dest (MkTyped.int size')], .temp dest)
      else
        let lengthSize := MkTyped.int (.memory 8)
        -- todo maybe add bounds checks here?
        let size' : Expr :=
          match e' with -- optimise if size is constant
          | .typed _tau (.const c) =>
            match c.toNat' with
            | some n => .memory (n * size.toNat + 8)
            | none   =>
              .binop .mul e' (MkTyped.int (.const size.toNat))
              |> MkTyped.int
              |> .binop .add lengthSize
          | .typed _tau _len =>
            .binop .mul e' (MkTyped.int (.const size.toNat))
            |> MkTyped.int
            |> .binop .add lengthSize
        let alloc := .alloc dest (MkTyped.int size')
        let storeLen := .store ⟨MkTyped.int (.temp dest), 0, none, 0⟩ e'
        let arr := .binop .add (MkTyped.int (.temp dest)) lengthSize
        return (stmts.append [alloc] |>.append [storeLen], arr)
    | none => panic! "IR Trans: Alloc array type size not known"

  | .dot _e _field
  | .deref _e
  | .index _e _indx =>
    let (stmts, address, checks) ← Addr.addr ⟨tau, exp⟩ 0 false
    let dest ← Env.Func.freshTemp
    return (stmts.append checks |>.append [.load dest address], .temp dest)

partial def texpr (texp : Tst.Typed Tst.Expr)
          : Env.Func ((List IrTree.Stmt) × IrTree.TypedExpr) :=
  MkTyped.expr (Trans.expr texp.typ texp.data) texp.typ

partial def args (args : List (Tst.Typed Tst.Expr))
         : Env.Func ((List IrTree.Stmt) × (List IrTree.TypedExpr)) := do
  match args with
  | [] => return ([], [])
  | arg :: args =>
    let (stmts, arg') ← Trans.texpr arg
    let (stmts', args') ← Trans.args args
    return (stmts.append stmts', arg' :: args')


/- returns the elaborated statements, address, and pending memory checks
 - This allows us to maintain the weird semantics for checks
 -/
partial def Addr.addr (texp : Tst.Typed Tst.Expr)
         (offset : UInt64)
         (check : Bool)
         : Env.Func (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  match texp.data with
  | .dot e field  => Addr.dot e field offset
  | .deref e      => Addr.deref e offset check
  | .index e indx => Addr.index e indx offset
  | _ => panic! "IR Trans: Attempted to address a non-pointer"

partial def Addr.dot (texp : Tst.Typed Tst.Expr)
               (field : Symbol)
               (offset : UInt64)
               : Env.Func
                  (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  let structs ← Env.Func.structs
  let struct :=
    match texp.typ with
    | .mem (.struct name) =>
      match structs.find? name with
      | some info => info
      | none => panic! s!"IR Trans: Could not find struct {name}"
    | _ => panic! s!"IR Trans: Expression {texp} does not have struct type"
  let foffset :=
    match struct.fields.find? field with
    | some foffset => foffset
    | none => panic! s!"IR Trans: Could not find field offset {field}"
  Addr.addr texp (offset + foffset) true

partial def Addr.deref (texp : Tst.Typed Tst.Expr)
         (offset : UInt64)
         (check : Bool)
         : Env.Func (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  let (stmts, texp') ← texpr texp
  let address := ⟨texp', offset, none, 0⟩
  if check
  then return (stmts.append [.check (.null texp')], address, [])
  else return (stmts, address, [.check (.null texp')])

partial def Addr.index (arr indx : Tst.Typed Tst.Expr)
               (offset : UInt64)
               : Env.Func
                (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  let (stmts1, arr') ← texpr arr
  let (stmts2, indx') ← texpr indx
  let scale ←
    match arr.typ with
    | .mem (.array tau) => do
      match ← Typ.size tau with
      | some s => pure s
      | none => panic! "IR Trans: Can't determine array element size"
    | _ => panic! s!"IR Trans: Indexing into non-array type"
  let checks := .check (.null arr') :: .check (.bounds arr' indx') :: []
  let address := ⟨arr', offset, some indx', scale.toNat⟩
  return (stmts1.append stmts2 |>.append checks, address, [])
end
end Trans
