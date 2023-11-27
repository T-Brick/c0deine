import Numbers
import C0deine.IrTree.IrTree
import C0deine.Type.Tst
import C0deine.Type.Typ
import C0deine.Context.Symbol
import C0deine.Context.Context
import C0deine.Context.Temp
import C0deine.Context.Label
import C0deine.Config.Config
import C0deine.Utils.Comparison
import C0deine.ControlFlow.CFG


namespace C0deine.IrTree.Trans

open ControlFlow.Block

structure StructInfo where
  size : UInt64
  alignment : UInt64
  fields : Symbol.Map UInt64
instance : Inhabited StructInfo where default := ⟨0, 0, Std.HashMap.empty⟩

namespace Env

structure Prog.State : Type where
  config : Config
  vars : Symbol.Map SizedTemp
  functions : Symbol.Map Label
  structs : Symbol.Map StructInfo


def Prog.State.new (config : Config) : Env.Prog.State where
  config := config
  vars := Std.HashMap.empty
  functions := Std.HashMap.empty
  structs := Std.HashMap.empty

def Prog := StateT Env.Prog.State Context
instance : Monad Env.Prog := show Monad (StateT _ _) from inferInstance


def Prog.config : Prog Config :=
  fun env => return ⟨env.config, env⟩

def Prog.new_var (size : ValueSize) (v : Symbol) : Prog SizedTemp :=
  fun env =>
    match env.vars.find? v with
    | some t => return (t, env)
    | none => do
      let t ← Temp.fresh
      let vt := ⟨size, t⟩
      let env' := {env with vars := env.vars.insert v vt}
      return (vt, env')

def Prog.var (v : Symbol) : Prog SizedTemp :=
  fun env =>
    match env.vars.find? v with
    | some t => return (t, env)
    | none => do
      let t ← Temp.fresh
      let vt := ⟨.double, t⟩
      let env' := {env with vars := env.vars.insert v vt}
      return (vt, env')

def Prog.addFunc (f : Symbol) (lbl : Label) : Prog Unit :=
  fun env =>
    let env' := {env with functions := env.functions.insert f lbl}
    return ((), env')

def Prog.func (f : Symbol) : Prog Label :=
  fun env =>
    match env.functions.find? f with
    | some l => return (l, env)
    | none => do
      let l ← Label.namedFresh ("_c0_" ++ f.name)
      let env' := {env with functions := env.functions.insert f l}
      return (l, env')

def Prog.freshTemp : Prog Temp :=
  fun env => return (← Temp.fresh, env)
def Prog.freshLabel : Prog Label :=
  fun env => return (← Label.fresh, env)
def Prog.namedLabel (name : String) : Prog Label :=
  fun env => return (← Label.namedFresh name, env)

def Prog.structs : Prog (Symbol.Map StructInfo) :=
  fun env => return ⟨env.structs, env⟩
def Prog.addStruct (name : Symbol) (struct : StructInfo) : Prog (Unit) :=
  fun env =>
    return ⟨(), {env with structs := env.structs.insert name struct}⟩


structure Func.State extends Env.Prog.State where
  blocks : Label.Map Block         -- finished blocks
  curBlockLabel : Label
  curBlockType : BlockType

def Func.State.new (config : Config) (label : Label) : Func.State :=
  { Prog.State.new config
    with blocks := Std.HashMap.empty
       , curBlockLabel := label
       , curBlockType := .funcEntry
  }

def Func := StateT Func.State Context
instance [Inhabited α] : Inhabited (Func α) :=
  show Inhabited (StateT _ _ α) from inferInstance
instance : Monad Func := show Monad (StateT _ _) from inferInstance

def Prog.startFunc (lbl : Label)
                   (type : BlockType)
                   (f : Func α)
                   : Prog (α × Label.Map Block) :=
  fun penv => do
    let fstate := ⟨penv, Std.HashMap.empty, lbl, type⟩
    let (res, fenv') ← f fstate
    return ((res, fenv'.blocks), fenv'.toState)

def Prog.toFunc (f : Prog α) : Func α :=
  fun env => do
    let (res, penv') ← f env.toState
    return (res, {env with toState := penv'})

def Func.unsafe : Func Bool := Prog.toFunc Prog.config |>.map (¬·.safe)
def Func.new_var (size : ValueSize) (v : Symbol) : Func SizedTemp :=
  Prog.toFunc (Prog.new_var size v)
def Func.var (v : Symbol) : Func SizedTemp := Prog.toFunc (Prog.var v)
def Func.func (f : Symbol) : Func Label := Prog.toFunc (Prog.func f)
def Func.freshTemp : Func Temp := Prog.toFunc Prog.freshTemp
def Func.freshLabel : Func Label := Prog.toFunc Prog.freshLabel
def Func.namedLabel (name : String) : Func Label :=
  Prog.toFunc (Prog.namedLabel name)
def Func.structs : Func (Symbol.Map StructInfo) := Prog.toFunc Prog.structs

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

def int (e : IrTree.Expr)  : Typ.Typed IrTree.Expr := ⟨.prim .int, e⟩
def bool (e : IrTree.Expr) : Typ.Typed IrTree.Expr := ⟨.prim .bool, e⟩
def null (e : IrTree.Expr) : Typ.Typed IrTree.Expr := ⟨.any, e⟩

def expr (env : Env.Func ((List IrTree.Stmt) × IrTree.Expr))
         (typ : Typ)
         : Env.Func ((List IrTree.Stmt) × Typ.Typed Expr) := do
  let (stmts, e') ← env
  return (stmts, ⟨typ, e'⟩)

end MkTyped

def Typ.size (tau : Typ) : Env.Prog (Option UInt64) := do
  match tau with
  | .any              => return none
  | .prim .int        => return some 4
  | .prim .bool       => return some 4 -- todo reduce to 1
  | .mem (.pointer _) => return some 8
  | .mem (.array _)   => return some 8
  | .mem (.struct n)  =>
    let s ← Env.Prog.structs
    return s.find? n |>.map (fun info => info.size)

def Typ.tempSize (tau : Typ) : Env.Prog ValueSize := do
  match ← Typ.size tau with
  | some 8 => return .quad
  | some 4 => return .double
  | some 2 => return .word
  | some 1 => return .byte
  | _      => return .double

def Elab.lvalue : Typ.Typed Tst.LValue → Typ.Typed Tst.Expr
  | .mk τ (.var name)      => .mk τ (.var name)
  | .mk τ (.dot lv field)  => .mk τ (.dot (Elab.lvalue lv) field)
  | .mk τ (.deref lv)      => .mk τ (.deref (Elab.lvalue lv))
  | .mk τ (.index lv indx) => .mk τ (.index (Elab.lvalue lv) indx)

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
    : (Typ.Typed Expr → Typ.Typed Expr → IrTree.Expr) ⊕ IrTree.EffectBinop :=
  match op with
  | .int iop   =>
    match binop_op_int iop with
    | .inl op => .inl (.binop op)
    | .inr op => .inr op
  | .bool .and => .inl IrTree.Expr.and
  | .bool .or  => .inl IrTree.Expr.or
  | .cmp c     => .inl (.binop (.comp c))

-- custom size definition to help prove termination
mutual
@[simp] def transSizeExpr (e : Tst.Expr) : Nat :=
  match e with
  | .num _        => 0
  | .var _        => 0
  | .true         => 0
  | .false        => 0
  | .null         => 0
  | .unop _ e     => 1 + transSizeTExpr e
  | .binop op l r =>
    match op with
    | .bool _        => 1 + 1 + (transSizeTExpr l) + 1 + (transSizeTExpr r)
    | _              => 1 + max (transSizeTExpr l) (transSizeTExpr r)
  | .ternop cc tt ff =>
    1 + (transSizeTExpr cc) + 1 + (transSizeTExpr tt) + 1 + (transSizeTExpr ff)
  | .app f as        => 1 + transSizeTExprList as
  | .alloc _         => 1
  | .alloc_array _ e => 1 + transSizeTExpr e
  | .dot e _field    => 2 + transSizeTExpr e
  | .deref e         => 2 + transSizeTExpr e
  | .index arr indx  => 2 + (transSizeTExpr arr) + (transSizeTExpr indx)

@[simp] def transSizeTExpr : Typ.Typed Tst.Expr → Nat
  | .mk _tau data => 1 + transSizeExpr data

@[simp] def transSizeTExprList : List (Typ.Typed Tst.Expr) → Nat
  | [] => 0
  | e :: es => 1 + max (transSizeTExpr e) (transSizeTExprList es)
end
termination_by
  transSizeExpr e => sizeOf e
  transSizeTExpr e => sizeOf e
  transSizeTExprList es => sizeOf es

theorem lt_one_nat_max_left (cc tt ff : Nat) : tt < 1 + cc + max tt ff := by
  have := Nat.le_max_left tt ff |> (Nat.le_iff_lt_or_eq).mp
  apply Or.elim this <;> intro h
  . simp [Nat.add_comm, Nat.lt_add_right _ _ (cc + 1) h]
  . simp [←h]

theorem lt_one_nat_max_right (cc tt ff : Nat) : ff < 1 + cc + max tt ff := by
  rw [Nat.max_comm]; exact lt_one_nat_max_left cc ff tt

mutual
def expr (tau : Typ)
         (acc : List IrTree.Stmt)
         (exp : Tst.Expr)
         : Env.Func ((List IrTree.Stmt) × IrTree.Expr) := do
  match exp with
  | .num (v : Int32) => return (acc, .const v)
  | .var (name : Symbol) => return (acc, .temp (← Env.Func.var name))
  | .«true» => return (acc, .byte 1)
  | .«false» => return (acc, .byte 0)
  | .null => return (acc, .memory 0)
  | .unop op e =>
    let (stmts, e') ← texpr acc e
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
    match h : op with
    | .bool .and =>
      have : 1 + transSizeTExpr l + max (transSizeTExpr r) 1
           < 1 + 1 + transSizeTExpr l + 1 + transSizeTExpr r := by
        let r := transSizeTExpr r
        have : max r 1 < 1 + 1 + r := by simp [Nat.add_comm]; linarith
        linarith
      ternary tau acc l r ⟨.prim .bool, .false⟩
    | .bool .or  =>
      have : 1 + transSizeTExpr l + max 1 (transSizeTExpr r)
           < 1 + 1 + transSizeTExpr l + 1 + transSizeTExpr r := by
        let r := transSizeTExpr r
        have : max 1 r < 1 + 1 + r := by simp [Nat.add_comm]; linarith
        linarith
      ternary tau acc l ⟨.prim .bool, .true⟩ r
    | .int _ | .cmp _ =>
      let (stmts1, l') ← texpr acc l
      let (stmts2, r') ← texpr stmts1 r
      match binop_op op with
      | .inl expr' => return (stmts2, expr' l' r') -- pure/boolean
      | .inr op' =>
        let size ← Env.Prog.toFunc (Typ.tempSize tau)
        let dest := ⟨size, ← Env.Func.freshTemp⟩
        let effect := .effect dest op' l' r'
        let shift := -- include bounds check
          match op' with
          | .lsh | .rsh => [.check (.shift r')]
          | .mod => [.check (.mod l' r')]
          | .div => []
        return (effect :: shift ++ stmts2, .temp dest)

  | .ternop cond tt ff => ternary tau acc cond tt ff

  | .app f as =>
    let (stmts, args') ← args acc as
    let func_lbl ← Env.Func.func f
    let dest ← Env.Func.freshTemp
    let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
    let call := .call sdest func_lbl args'
    let size ← Env.Prog.toFunc (Typ.tempSize tau)
    return (call :: stmts, .temp ⟨size, dest⟩)

  | .alloc ty =>
    match ← Env.Prog.toFunc (Typ.size ty) with
    | some size =>
      let dest ← Env.Func.freshTemp
      let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
      return (.alloc dest (MkTyped.int (.memory size.toNat)) :: acc
             , .temp sdest)
    | none => panic! "IR Trans: Alloc type size not known"

  | .alloc_array ty e =>
    match ← Env.Prog.toFunc (Typ.size ty) with
    | some size =>
      let (stmts, e') ← texpr acc e
      let dest ← Env.Func.freshTemp
      if ← Env.Func.unsafe
      then
        let size' := -- don't need to store length if unsafe
          match e'.data with -- optimise if size is constant
          | .const c =>
            match c.toNat' with
            | some n => .memory (n * size.toNat)
            | none   => .binop .mul e' (MkTyped.int (.const size.toNat))
          | _ => .binop .mul e' (MkTyped.int (.const size.toNat))
        let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
        return (.alloc dest (MkTyped.int size') :: stmts, .temp sdest)
      else
        let lengthSize := MkTyped.int (.memory 8)
        -- todo maybe add bounds checks here?
        let size' : Expr :=
          match e'.data with -- optimise if size is constant
          | .const c =>
            match c.toNat' with
            | some n => .memory (n * size.toNat + 8)
            | none   =>
              .binop .mul e' (MkTyped.int (.const size.toNat))
              |> MkTyped.int
              |> .binop .add lengthSize
          | _ =>
            .binop .mul e' (MkTyped.int (.const size.toNat))
            |> MkTyped.int
            |> .binop .add lengthSize
        let alloc := .alloc dest (MkTyped.int size')
        let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
        let storeLen := .store ⟨MkTyped.int (.temp sdest), 0, none, 0⟩ e'
        let arr := .binop .add (MkTyped.int (.temp sdest)) lengthSize
        return (storeLen :: alloc :: stmts, arr)
    | none => panic! "IR Trans: Alloc array type size not known"

  | .dot e field =>
    let (stmts, address, checks) ← Addr.dot acc e field 0
    let dest ← Env.Func.freshTemp
    let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
    return (.load sdest address :: checks ++ stmts, .temp sdest)

  | .deref e =>
    let (stmts, address, checks) ← Addr.deref acc e 0 false
    let dest ← Env.Func.freshTemp
    let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
    return (.load sdest address :: checks ++ stmts, .temp sdest)

  | .index arr indx =>
    let (stmts, address, checks) ← Addr.index acc arr indx 0
    let dest ← Env.Func.freshTemp
    let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
    return (.load sdest address :: checks ++ stmts, .temp sdest)

def ternary (tau : Typ) (acc : List IrTree.Stmt)
            (cond tt ff : Typ.Typed Tst.Expr)
            : Env.Func ((List IrTree.Stmt) × IrTree.Expr) := do
    let lT ← Env.Func.freshLabel
    let lF ← Env.Func.freshLabel
    let lN ← Env.Func.freshLabel
    let dest ← Env.Func.freshTemp
    let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩

    let (stmts, cond') ← texpr acc cond
    let cond_temp ← Env.Func.freshTemp
    let scond_temp := ⟨← Env.Prog.toFunc (Typ.tempSize cond.type), cond_temp⟩
    let condT := .move scond_temp cond'
    let exit := .cjump cond_temp none lT lF
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, (condT :: stmts).reverse, exit⟩
    let () ← Env.Func.addBlock block lT .ternaryTrue

    have :=
      lt_one_nat_max_left (transSizeTExpr cond)
        (transSizeTExpr tt)
        (transSizeTExpr ff)
    let (stmtsT, tt') ← texpr [] tt
    let exitT := .jump lN
    let destT := .move sdest tt'
    let blockT := ⟨lT, .ternaryTrue, (destT :: stmtsT).reverse, exitT⟩
    let () ← Env.Func.addBlock blockT lF .ternaryFalse

    have :=
      lt_one_nat_max_right (transSizeTExpr cond)
        (transSizeTExpr tt)
        (transSizeTExpr ff)
    let (stmtsF, ff') ← texpr [] ff
    let exitF := .jump lN
    let destF := .move sdest ff'
    let blockF := ⟨lF, .ternaryFalse, (destF :: stmtsF).reverse, exitF⟩
    let () ← Env.Func.addBlock blockF lN .afterTernary

    return ([], .temp sdest)

def texpr (acc : List IrTree.Stmt)
          : Typ.Typed Tst.Expr
          → Env.Func ((List IrTree.Stmt) × Typ.Typed Expr)
  | .mk τ e => MkTyped.expr (expr τ acc e) τ

def args (acc : List IrTree.Stmt) (as : List (Typ.Typed Tst.Expr))
         : Env.Func ((List IrTree.Stmt) × (List (Typ.Typed Expr))) := do
  match as with
  | [] => return ([], [])
  | arg :: as =>
    let (stmts, arg') ← texpr acc arg
    let (stmts', args') ← args stmts as
    return (stmts', arg' :: args')


/- returns the elaborated statements, address, and pending memory checks
 - This allows us to maintain the weird semantics for checks
 -/
def Addr.addr (_tau : Typ) (acc : List IrTree.Stmt)
         (e : Tst.Expr)
         (offset : UInt64)
         (check : Bool)
         : Env.Func (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  match e with
  | .dot e field  => Addr.dot acc e field offset
  | .deref e      => Addr.deref acc e offset check
  | .index e indx => Addr.index acc e indx offset
  | _ => panic! "IR Trans: Attempted to address a non-pointer"

def Addr.dot (acc : List IrTree.Stmt)
             (texp : Typ.Typed Tst.Expr)
             (field : Symbol)
             (offset : UInt64)
             : Env.Func
                (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  let structs ← Env.Func.structs
  let struct :=
    match texp.type with
    | .mem (.struct name) =>
      match structs.find? name with
      | some info => info
      | none => panic! s!"IR Trans: Could not find struct {name}"
    | _ => panic! s!"IR Trans: Expression {texp} does not have struct type"
  let foffset :=
    match struct.fields.find? field with
    | some foffset => foffset
    | none => panic! s!"IR Trans: Could not find field offset {field}"
  match texp with
  | .mk τ e => Addr.addr τ acc e (offset + foffset) true

def Addr.deref (acc : List IrTree.Stmt)
         (texp : Typ.Typed Tst.Expr)
         (offset : UInt64)
         (check : Bool)
         : Env.Func (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  let (stmts, texp') ← texpr acc texp
  let address := ⟨texp', offset, none, 0⟩
  if check
  then return (.check (.null texp') :: stmts, address, [])
  else return (stmts, address, [.check (.null texp')])

def Addr.index (acc : List IrTree.Stmt)
               (arr indx : Typ.Typed Tst.Expr)
               (offset : UInt64)
               : Env.Func
                  (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  let (stmts1, arr') ← texpr acc arr
  let (stmts2, indx') ← texpr stmts1 indx
  let scale ←
    match arr.type with
    | .mem (.array tau) => do
      match ← Env.Prog.toFunc (Typ.size tau) with
      | some s => pure s
      | none => panic! "IR Trans: Can't determine array element size"
    | _ => panic! s!"IR Trans: Indexing into non-array type"
  let stmts' :=  .check (.bounds arr' indx') :: .check (.null arr') :: stmts2
  let address := ⟨arr', offset, some indx', scale.toNat⟩
  return (stmts', address, [])
end
termination_by
  expr tau acc e           => transSizeExpr e
  ternary tau acc cc tt ff =>
    1 + transSizeTExpr cc + max (transSizeTExpr tt) (transSizeTExpr ff)
  texpr acc te             => transSizeTExpr te
  args acc as              => transSizeTExprList as
  Addr.addr tau acc e _ _  => 1 + transSizeExpr e
  Addr.dot acc e _ _       => 1 + transSizeTExpr e
  Addr.deref acc e _ _     => 1 + transSizeTExpr e
  Addr.index acc arr i _   => 1 + transSizeTExpr arr + transSizeTExpr i

def Addr.taddr (acc : List IrTree.Stmt)
    : Typ.Typed Tst.Expr → UInt64 → Bool
    → Env.Func (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt)
  | .mk τ e => Addr.addr τ acc e

mutual
def stmt (past : List IrTree.Stmt) (stm : Tst.Stmt) : Env.Func (List IrTree.Stmt) := do
  match stm with
  | .decl name init body =>
    let t ←
      Env.Func.new_var (← Env.Prog.toFunc (Typ.tempSize name.type)) name.data
    let init_stmts ← do
      match init with
      | some i =>
        let (stmts, res) ← texpr past i
        pure (.move t res :: stmts)
      | none => pure []
    stmts init_stmts body
  | .assign tlv oop rhs =>
    match tlv.data, oop with
    | .var name, none =>
      let dest ← Env.Func.var name
      let (stms, src) ← texpr past rhs
      return .move dest src :: stms
    | .var _name, some _ =>
      panic! s!"IR Trans: 'x += e' should have been elaborated away"
    | _, _ =>
      let lhs' := Elab.lvalue tlv
      let (stms1, dest, checks) ← Addr.taddr past lhs' 0 false
      let (stms2, src) ← texpr stms1 rhs
      let size ← Env.Prog.toFunc (Typ.tempSize tlv.type)
      match oop.map binop_op_int with
      | none => return .store dest src :: checks ++ stms2
      | some (.inl pure) =>
        let temp := ⟨size, ← Env.Func.freshTemp⟩
        let ttemp := ⟨rhs.type, .temp temp⟩
        let load := .load temp dest
        let src' := ⟨lhs'.type, .binop pure ttemp src⟩
        let store := .store dest src'
        return store :: load :: checks ++ stms2
      | some (.inr impure) =>
        let t1 := ⟨size, ← Env.Func.freshTemp⟩
        let t2 := ⟨size, ← Env.Func.freshTemp⟩
        let tt1 := ⟨rhs.type, .temp t1⟩
        let tt2 := ⟨rhs.type, .temp t2⟩
        let load : IrTree.Stmt := .load t1 dest
        let effect := .effect t2 impure tt1 src
        let store := .store dest tt2
        return store :: effect :: load :: checks ++ stms2

  | .ite cond tt ff =>
    let tLbl  ← Env.Func.freshLabel
    let fLbl  ← Env.Func.freshLabel
    let after ← Env.Func.freshLabel

    let (cstms, cond') ← texpr past cond
    let cond_temp ← Env.Func.freshTemp
    let scond_temp := ⟨← Env.Prog.toFunc (Typ.tempSize cond.type), cond_temp⟩
    let condT := .move scond_temp cond'

    let exit := .cjump cond_temp none tLbl fLbl
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, (condT :: cstms).reverse, exit⟩
    let () ← Env.Func.addBlock block tLbl .thenClause

    let tt' ← stmts [] tt
    let exit := .jump after
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, tt'.reverse, exit⟩
    let () ← Env.Func.addBlock block fLbl .elseClause

    let ff' ← stmts [] ff
    let exit := .jump after
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, ff'.reverse, exit⟩
    let () ← Env.Func.addBlock block after .afterITE
    return []

  | .while cond body =>
    -- elaborate to a `do while` which saves jumps
    let loopBody  ← Env.Func.freshLabel
    let afterLoop ← Env.Func.freshLabel

    let (cstms, cond') ← texpr past cond
    let cond_temp ← Env.Func.freshTemp
    let scond_temp := ⟨← Env.Prog.toFunc (Typ.tempSize cond.type), cond_temp⟩
    let condT := .move scond_temp cond'

    let exit := .cjump cond_temp (some true) loopBody afterLoop
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, (condT :: cstms).reverse, exit⟩
    let () ← Env.Func.addBlock block loopBody .loop

    let body' ← stmts [] body
    let exit := .cjump cond_temp (some true) loopBody afterLoop
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, (condT :: body').reverse, exit⟩
    let () ← Env.Func.addBlock block afterLoop .afterLoop
    return []

  | .«return» .none =>
    let exit := .«return» none
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, past.reverse, exit⟩
    let nextLbl ← Env.Func.freshLabel
    let () ← Env.Func.addBlock block nextLbl .afterRet
    return []

  | .«return» (.some e) =>
    let (stms, e') ← texpr past e
    let exit := .«return» (some e')
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, stms.reverse, exit⟩
    let nextLbl ← Env.Func.freshLabel
    let () ← Env.Func.addBlock block nextLbl .afterRet
    return []

  | .assert e =>
    let after ← Env.Func.freshLabel
    let assertLbl := Label.abort

    let (stms, e') ← texpr past e
    let cond_temp ← Env.Func.freshTemp
    let scond_temp := ⟨← Env.Prog.toFunc (Typ.tempSize e.type), cond_temp⟩
    let condT := .move scond_temp e'

    let exit := .cjump cond_temp (some true) after assertLbl
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, (condT :: stms).reverse, exit⟩
    let () ← Env.Func.addBlock block after curType
    return []

  | .expr e =>
    let (stms, _) ← texpr past e -- drop pure expression
    return stms

def stmts (past : List IrTree.Stmt)
          (stms : List Tst.Stmt)
          : Env.Func (List IrTree.Stmt) := do
  match stms with
  | []      => return past
  | s :: ss =>
    let past' ← stmt past s
    stmts past' ss
end
termination_by
  stmt ctx s   => sizeOf s
  stmts ctx ss => sizeOf ss

def dec_args (args : List (Typ.Typed Symbol)) : Env.Prog (List SizedTemp) := do
  match args with
  | [] => return []
  | arg :: args =>
    let size ← Typ.tempSize arg.type
    let t ← Env.Prog.new_var size arg.data
    let ts ← dec_args args
    return t :: ts

def gdecl (header : Bool) (glbl : Tst.GDecl) : Env.Prog (Option Func) := do
  match glbl with
  | .fdecl fdec =>
    let label ←
      if header
      then Env.Prog.namedLabel fdec.name.name
      else Env.Prog.namedLabel s!"_c0_{fdec.name.name}"
    let () ← Env.Prog.addFunc fdec.name label
    return none
  | .fdef fdef =>
    let label ← Env.Prog.namedLabel s!"_c0_{fdef.name.name}"
    let args ← dec_args fdef.params
    let entry ← Env.Prog.freshLabel
    let (_remain, blocks) ←
      Env.Prog.startFunc entry .funcEntry (stmts [] fdef.body)
    let () ← Env.Prog.addFunc fdef.name label
    let res ← fdef.type.mapM Typ.tempSize
    return some ⟨label, entry, args, blocks, res, sorry⟩
  | .sdef sd =>
    let alignList ← sd.fields |>.mapM (fun ts =>
        match ts.type with
        | .mem (.struct str) => do
          match (← Env.Prog.structs).find? str with
          | some s' => pure s'.alignment
          | none    => panic! s!"IR Trans: {sd.name} field has undefined struct"
        | _ =>
          match ts.type.sizeof with
          | some n => pure (UInt64.ofNat n)
          | _ => panic! s!"IR Trans: {sd.name} has malformed field types"
      )
    let alignment := alignList.foldl max (UInt64.ofNat 1)

    let align : UInt64 → UInt64 → UInt64 := fun off a => off + (a - off) % a

    let (size, offsetsR) := alignList.zip sd.fields
      |>.foldl (fun (offset, acc) (a, f) =>
        let size :=
          match f.type.sizeof with
          | some n => UInt64.ofNat n
          | _ => panic! s!"IR Trans: {sd.name} has malformed field types"
        let offset' := align offset a
        (offset' + size, (f.data, offset') :: acc)
      ) (UInt64.ofNat 0, [])
    let size' := align size alignment
    let offsets := Std.HashMap.ofList offsetsR
    let () ← Env.Prog.addStruct sd.name ⟨size', alignment, offsets⟩
    return none

def prog (config : Config) (tst : Tst.Prog) : Context IrTree.Prog := do
  let initState := Env.Prog.State.new config
  let transOne := fun header (state, acc) gd => do
      let (fOpt, state') ← gdecl header gd state
      match fOpt with
      | some f => pure (state', f :: acc)
      | none   => pure (state', acc)
  let (_state, funcsR) ←
    tst.header.foldlM (transOne true) (initState, [])
    |>.bind (tst.body.foldlM (transOne false))
  return funcsR.reverse
