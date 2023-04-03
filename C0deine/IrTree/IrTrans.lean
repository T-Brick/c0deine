
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
  vars : Symbol.Map SizedTemp
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

def Func.new_var (size : ValueSize) (v : Symbol) : Env.Func SizedTemp :=
  fun env =>
    match env.vars.find? v with
    | some t => return (t, env)
    | none => do
      let t ← Temp.fresh
      let vt := ⟨size, t⟩
      let env' := {env with vars := env.vars.insert v vt}
      return (vt, env')

def Func.var (v : Symbol) : Env.Func SizedTemp :=
  fun env =>
    match env.vars.find? v with
    | some t => return (t, env)
    | none => do
      let t ← Temp.fresh
      let vt := ⟨.double, t⟩
      let env' := {env with vars := env.vars.insert v vt}
      return (vt, env')

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

def Typ.tempSize (tau : Typ) : Env.Func ValueSize := do
  match ← Typ.size tau with
  | some 8 => return .quad
  | some 4 => return .double
  | some 2 => return .word
  | some 1 => return .byte
  | _      => return .double

def Elab.lvalue (tlv : Tst.Typed Tst.LValue) : Tst.Typed Tst.Expr :=
  .typed tlv.typ (
    match tlv with
    | .typed _ lv =>
      match lv with
      | .var name      => .var name
      | .dot lv field  => .dot (Elab.lvalue lv) field
      | .deref lv      => .deref (Elab.lvalue lv)
      | .index lv indx => .index (Elab.lvalue lv) indx
  )
termination_by Elab.lvalue tlv => sizeOf tlv

namespace Trans

def binop_op_int (op : Tst.BinOp.Int)
                  : IrTree.PureBinop ⊕ IrTree.EffectBinop :=
  match op with
  | .plus  => .inl (.add)
  | .minus => .inl (.sub)
  | .times => .inl (.mul)
  | .div   => .inr (.div)
  | .mod   => .inr (.mod)
  | .and   => .inl (.and)
  | .xor   => .inl (.xor)
  | .or    => .inl (.or)
  | .lsh   => .inr (.lsh)
  | .rsh   => .inr (.rsh)

def binop_op (op : Tst.BinOp)
             : IrTree.PureBinop ⊕ IrTree.EffectBinop :=
  match op with
  | .int iop   => Trans.binop_op_int iop
  | .bool .and => .inl .and
  | .bool .or  => .inl .or
  | .cmp c     => .inl (.comp c)

mutual
partial def expr (tau : Typ)
         (exp : Tst.Expr)
         : Env.Func ((List IrTree.Stmt) × IrTree.Expr) := do
  match exp with
  | .num (v : Int32) => return ([], .const v)
  | .var (name : Symbol) =>
    let size ← Typ.tempSize tau
    return ([], .temp (← Env.Func.var name))
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
      let size ← Typ.tempSize tau
      let dest := ⟨size, ← Env.Func.freshTemp⟩
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
    let sdest := ⟨← Typ.tempSize tau, dest⟩

    let (stmts, cond') ← Trans.texpr cond
    let exit := .cjump cond' none lT lF
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, stmts, exit⟩
    let () ← Env.Func.addBlock block lT .ternaryTrue

    let (stmtsT, tt') ← Trans.texpr tt
    let exitT := .jump lN
    let destT := .move sdest tt'
    let blockT := ⟨lT, .ternaryTrue, stmtsT.append [destT], exitT⟩
    let () ← Env.Func.addBlock blockT lF .ternaryFalse

    let (stmtsF, ff') ← Trans.texpr ff
    let exitF := .jump lN
    let destF := .move sdest ff'
    let blockF := ⟨lF, .ternaryFalse, stmtsF.append [destF], exitF⟩
    let () ← Env.Func.addBlock blockF lN .afterTernary

    return ([], .temp sdest)

  | .app f args =>
    let (stmts, args') ← Trans.args args
    let func_lbl ← Env.Func.func f
    let dest ← Env.Func.freshTemp
    let sdest := ⟨← Typ.tempSize tau, dest⟩
    let call := .call sdest func_lbl args'
    let size ← Typ.tempSize tau
    return (stmts.append [call], .temp ⟨size, dest⟩)

  | .alloc ty =>
    match ← Typ.size ty with
    | some size =>
      let dest ← Env.Func.freshTemp
      let sdest := ⟨← Typ.tempSize tau, dest⟩
      return ([.alloc dest (MkTyped.int (.memory size.toNat))], .temp sdest)
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
        let sdest := ⟨← Typ.tempSize tau, dest⟩
        return (stmts.append [.alloc dest (MkTyped.int size')], .temp sdest)
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
        let sdest := ⟨← Typ.tempSize tau, dest⟩
        let storeLen := .store ⟨MkTyped.int (.temp sdest), 0, none, 0⟩ e'
        let arr := .binop .add (MkTyped.int (.temp sdest)) lengthSize
        return (stmts.append [alloc] |>.append [storeLen], arr)
    | none => panic! "IR Trans: Alloc array type size not known"

  | .dot _e _field
  | .deref _e
  | .index _e _indx =>
    let (stmts, address, checks) ← Addr.addr ⟨tau, exp⟩ 0 false
    let dest ← Env.Func.freshTemp
    let sdest := ⟨← Typ.tempSize tau, dest⟩
    return (stmts.append checks |>.append [.load sdest address], .temp sdest)

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

mutual
def stmt (past : List IrTree.Stmt) (stm : Tst.Stmt) : Env.Func (List IrTree.Stmt) := do
  match stm with
  | .decl name init body =>
    let t ← Env.Func.new_var (← Typ.tempSize name.typ) name.data
    let init_stmts ← do
      match init with
      | some i =>
        let (stmts, res) ← Trans.texpr i
        pure (stmts.append [.move t res])
      | none => pure []
    stmts (past.append init_stmts) body
  | .assign tlv oop rhs =>
    match tlv.data, oop with
    | .var name, none =>
      let dest ← Env.Func.var name
      let (stms, src) ← texpr rhs
      return stms.append [.move dest src]
    | .var _name, some _ =>
      panic! s!"IR Trans: 'x += e' should have been elaborated away"
    | _, _ =>
      let lhs' := Elab.lvalue tlv
      let (stms1, dest, checks) ← Addr.addr lhs' 0 false
      let (stms2, src) ← texpr rhs
      let size ← Typ.tempSize tlv.typ
      match oop.map binop_op_int with
      | none =>
        return stms1.append stms2
          |>.append checks
          |>.append [.store dest src]
      | some (.inl pure) =>
        let temp := ⟨size, ← Env.Func.freshTemp⟩
        let ttemp := ⟨rhs.typ, .temp temp⟩
        let load := .load temp dest
        let src' := ⟨lhs'.typ, .binop pure ttemp src⟩
        let store := .store dest src'
        return stms1.append stms2
          |>.append checks
          |>.append [load, store]
      | some (.inr impure) =>
        let t1 := ⟨size, ← Env.Func.freshTemp⟩
        let t2 := ⟨size, ← Env.Func.freshTemp⟩
        let tt1 := ⟨rhs.typ, .temp t1⟩
        let tt2 := ⟨rhs.typ, .temp t2⟩
        let load : IrTree.Stmt := .load t1 dest
        let effect := .effect t2 impure tt1 src
        let store := .store dest tt2
        return stms1.append stms2
          |>.append checks
          |>.append [load]
          |>.append [effect, store]

  | .ite cond tt ff =>
    let tLbl  ← Env.Func.freshLabel
    let fLbl  ← Env.Func.freshLabel
    let after ← Env.Func.freshLabel

    let (cstms, cond') ← texpr cond
    let exit := .cjump cond' none tLbl fLbl
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, past.append cstms, exit⟩
    let () ← Env.Func.addBlock block tLbl .thenClause

    let tt' ← stmts [] tt
    let exit := .jump after
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, tt', exit⟩
    let () ← Env.Func.addBlock block fLbl .elseClause

    let ff' ← stmts [] ff
    let exit := .jump after
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, ff', exit⟩
    let () ← Env.Func.addBlock block after .afterITE
    return []

  | .while cond body =>
    -- elaborate to a `do while` which saves jumps
    let loopBody  ← Env.Func.freshLabel
    let afterLoop ← Env.Func.freshLabel

    let (cstms, cond') ← texpr cond

    let exit := .cjump cond' (some true) loopBody afterLoop
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, past.append cstms, exit⟩
    let () ← Env.Func.addBlock block loopBody .loop

    let body' ← stmts [] body
    let exit := .cjump cond' (some true) loopBody afterLoop
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, body'.append cstms, exit⟩
    let () ← Env.Func.addBlock block afterLoop .afterLoop
    return []

  | .«return» .none =>
    let exit := .«return» none
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, past, exit⟩
    let nextLbl ← Env.Func.freshLabel
    let () ← Env.Func.addBlock block nextLbl .afterRet
    return []

  | .«return» (.some e) =>
    let (stms, e') ← texpr e
    let exit := .«return» (some e')
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, past.append stms, exit⟩
    let nextLbl ← Env.Func.freshLabel
    let () ← Env.Func.addBlock block nextLbl .afterRet
    return []

  | .assert e =>
    let after ← Env.Func.freshLabel
    let assertLbl := Label.abort

    let (stms, e') ← texpr e
    let exit := .cjump e' (some true) after assertLbl
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, past.append stms, exit⟩
    let () ← Env.Func.addBlock block after curType
    return []

  | .expr e =>
    let (stms, _) ← texpr e -- drop pure expression
    return past.append stms

def stmts (past : List IrTree.Stmt)
          (stms : List Tst.Stmt)
          : Env.Func (List IrTree.Stmt) := do
  match stms with
  | []      => return past
  | s :: ss =>
    let past' ← stmt past s
    stmts past' ss

end


end Trans
