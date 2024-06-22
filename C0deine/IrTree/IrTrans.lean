/- C0deine - IrTrans
   Translates the Typed Syntax Tree into the IRTree. Most optimisations
   are intended to be performed on this representation.
   - Thea Brick
 -/
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
instance : Inhabited StructInfo where default := ⟨0, 0, Batteries.HashMap.empty⟩

namespace Env

structure Prog.State : Type where
  config    : Config
  vars      : Symbol.Map SizedTemp
  functions : Symbol.Map Label
  structs   : Symbol.Map StructInfo
  str_map   : List (String × UInt64)


def Prog.State.new (config : Config) (str_map : List (String × UInt64))
                   : Env.Prog.State where
  config    := config
  vars      := Batteries.HashMap.empty
  functions := Batteries.HashMap.empty
  structs   := Batteries.HashMap.empty
  str_map   := str_map

def Prog := StateT Env.Prog.State Context
instance : Monad Env.Prog := show Monad (StateT _ _) from inferInstance


def Prog.config : Prog Config :=
  fun env => return ⟨env.config, env⟩

def Prog.new_var (size : ValueSize) (v : Typ.Typed Symbol) : Prog SizedTemp :=
  fun env =>
    match env.vars.find? v.data with
    | some t => return (t, env)
    | none => do
      let t ← Temp.namedFresh v.data.name
      let vt := ⟨size, t⟩
      let env' := {env with vars := env.vars.insert v.data vt}
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
def Prog.namedTemp (name : String) : Prog Temp :=
  fun env => return (← Temp.namedFresh name, env)

def Prog.freshLabel : Prog Label :=
  fun env => return (← Label.fresh, env)
def Prog.namedLabel (name : String) : Prog Label :=
  fun env => return (← Label.namedFresh name, env)

def Prog.structs : Prog (Symbol.Map StructInfo) :=
  fun env => return ⟨env.structs, env⟩
def Prog.addStruct (name : Symbol) (struct : StructInfo) : Prog (Unit) :=
  fun env =>
    return ⟨(), {env with structs := env.structs.insert name struct}⟩

def Prog.string_offset (s : String) : Prog UInt64 :=
  fun env =>
    match env.str_map.find? (fun (s', _) => s = s') with
    | .some (_, offset) => return ⟨offset, env⟩
    | .none             =>
      return ⟨panic! s!"Couldn't find String {s} offset", env⟩

structure Func.State extends Env.Prog.State where
  blocks : Label.Map Block         -- finished blocks
  curBlockLabel : Label
  curBlockType : BlockType

def Func.State.new (config : Config)
                   (label : Label)
                   (str_map : List (String × UInt64))
                   : Func.State :=
  { Prog.State.new config str_map
    with blocks := Batteries.HashMap.empty
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
    let fstate := ⟨penv, Batteries.HashMap.empty, lbl, type⟩
    let (res, fenv') ← f fstate
    return ((res, fenv'.blocks), fenv'.toState)

def Prog.toFunc (f : Prog α) : Func α :=
  fun env => do
    let (res, penv') ← f env.toState
    return (res, {env with toState := penv'})

def Func.unsafe : Func Bool :=
  Prog.toFunc Prog.config |>.map (¬·.safe)
def Func.dynCheckContracts : Func Bool :=
  Prog.toFunc Prog.config |>.map (·.dynCheckContracts)
def Func.checkAssertsWhenUnsafe : Func Bool :=
  Prog.toFunc Prog.config |>.map (·.checkAssertsWhenUnsafe)

def Func.new_var (size : ValueSize) (v : Typ.Typed Symbol) : Func SizedTemp :=
  Prog.toFunc (Prog.new_var size v)
def Func.var (v : Symbol) : Func SizedTemp := Prog.toFunc (Prog.var v)
def Func.func (f : Symbol) : Func Label := Prog.toFunc (Prog.func f)

def Func.freshTemp : Func Temp := Prog.toFunc Prog.freshTemp
def Func.namedTemp (name : String) : Func Temp :=
  Prog.toFunc (Prog.namedTemp name)

def Func.freshLabel : Func Label := Prog.toFunc Prog.freshLabel
def Func.namedLabel (name : String) : Func Label :=
  Prog.toFunc (Prog.namedLabel name)

def Func.structs : Func (Symbol.Map StructInfo) := Prog.toFunc Prog.structs
def Func.string_offset : String → Func UInt64 :=
  Prog.toFunc ∘ Prog.string_offset

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

def String.mapping (strings : List String)
    : UInt64 × List (String × UInt64) :=
  let (size, res) := strings.foldl (fun (offset, acc) s =>
      ( offset + (UInt64.ofNat s.length) + 1 -- add 1 for null terminator
      , (s, offset) :: acc
      )
    ) ((8 : UInt64), []) -- start 8-bytes to avoid NULL
  (size + (8 - size) % 8, res.reverse) -- 8-byte align the size.

namespace MkTyped

def int  (e : IrTree.Expr) : Typ.Typed IrTree.Expr := ⟨.prim .int, e⟩
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
  | .prim .bool       => return some 1
  | .prim .char       => return some 1
  | .prim .string     => return some 8
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

def Elab.lvalue : Tst.LValue Δ Γ τ → Tst.Expr Δ Γ τ
  | .var name h            => .var name h
  | .dot hτ lv field h₁ h₂ => .dot hτ (Elab.lvalue lv) field h₁ h₂
  | .deref hτ lv           => .deref hτ (Elab.lvalue lv)
  | .index hτ₁ hτ₂ lv indx => .index hτ₁ hτ₂ (Elab.lvalue lv) indx.val

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

-- custom size definition to help prove termination
mutual
partial def transSizeExpr (e : Tst.Expr Δ Γ τ) : Nat :=
  match e with
  | .num _ _                 => 0
  | .char _ _                => 0
  | .str _ _                 => 0
  | .var _ _                 => 0
  | .true _                  => 0
  | .false _                 => 0
  | .null _                  => 0
  | .unop_int _ _ _ e        => 1 + transSizeExpr e
  | .unop_bool _ _ _ e       => 1 + transSizeExpr e
  | .binop_bool _ _ _ op l r => 1 + 1 + (transSizeExpr l) + 1 + (transSizeExpr r)
  | .binop_int _ _ _ _ l r
  | .binop_eq _ _ _ l r _ _
  | .binop_rel_int _ _ _ _ _ l r
  | .binop_rel_char _ _ _ _ _ l r => 1 + max (transSizeExpr l) (transSizeExpr r)
  | .ternop _ _ cc tt ff _  =>
    1 + (transSizeExpr cc) + 1 + (transSizeExpr tt) + 1 + (transSizeExpr ff)
  | .app _f _ τs _ as =>
    let _as' : (i : Fin _) → Tst.Expr Δ Γ (τs i) :=
      fun i => as i
    1
    -- 1 + transSizeArgs τs as'
  | .alloc _            => 1
  | .alloc_array _ _ e  => 1 + transSizeExpr e
  | .dot _ e _ _ _      => 2 + transSizeExpr e
  | .deref _ e          => 2 + transSizeExpr e
  | .index _ _ arr indx => 2 + (transSizeExpr arr) + (transSizeExpr indx)
  | .result _           => 0
  | .length _ e         => 1 + transSizeExpr e

partial def transSizeArgs
    (τs : List Typ)
    (as : (i : Fin τs.length) → Tst.Expr Δ Γ (τs.get i))
    : Nat :=
  match τs with
  | [] => 0
  | τ :: rest =>
    let se := transSizeExpr (as ⟨0, by simp⟩)
    let ses := transSizeArgs rest (fun i =>
        as ⟨Nat.succ i, by
          simp only [
            Nat.succ_eq_add_one,
            List.length_cons,
            add_lt_add_iff_right,
            Fin.is_lt
          ]⟩
      )
    1 + max se ses
end
-- termination_by
  -- transSizeExpr e => sizeOf e
  -- transSizeArgs τs as => sizeOf (List.ofFn (fun i => sizeOf (as i)))

theorem lt_one_nat_max_left (cc tt ff : Nat) : tt < 1 + cc + max tt ff := by
  have := Nat.le_max_left tt ff |> (Nat.le_iff_lt_or_eq).mp
  apply Or.elim this <;> intro h
  . simp [Nat.add_comm, Nat.lt_add_right _ h]
  . simp [←h]

theorem lt_one_nat_max_right (cc tt ff : Nat) : ff < 1 + cc + max tt ff := by
  rw [Nat.max_comm]; exact lt_one_nat_max_left cc ff tt

mutual
partial def expr (tau : Typ)
         (acc : List IrTree.Stmt)
         (exp : Tst.Expr Δ Γ tau)
         : Env.Func ((List IrTree.Stmt) × IrTree.Expr) := do
  match exp with
  | .num _ v     => return (acc, .const v)
  | .char _ c    =>
    if h : c.val.val < 256
    then return (acc, .byte (c.toUInt8 h))
    else panic! s!"IR Trans: Char {c} is too large!"
  | .str _ s     =>
    let src ← Env.Func.string_offset s
    let len := s.length + 1

    let res ← Env.Func.freshTemp
    let sres := ⟨.quad, res⟩
    let tres := ⟨.prim .string, .temp sres⟩
    let tsrc := ⟨.prim .string, .memory src.toNat⟩

    let alloc := .alloc res ⟨.prim .int, .const len⟩
    let copy  := .copy ⟨tres, 0, .none, 1⟩ ⟨tsrc, 0, .none, 1⟩ len

    return (copy :: alloc :: acc, .temp sres)
  | .var name _  => return (acc, .temp (← Env.Func.var name))
  | .«true» _      => return (acc, .byte 1)
  | .«false» _     => return (acc, .byte 0)
  | .null _        => return (acc, .memory 0)
  | .unop_int _ _ op e =>
    let (stmts, e') ← texpr acc e
    match op with
    | .neg =>
      let c := MkTyped.int (.const 0)
      return (stmts, .binop .sub c e')
    | .not => -- ~x ---> x ^ -1
      let c := MkTyped.int (.const (-1))
      return (stmts, .binop .xor e' c)

  | .unop_bool _ _ .neg e => -- !x ---> x == 0
      let (stmts, e') ← texpr acc e
      let c := MkTyped.int (.const 0)
      return (stmts, .binop (.comp .equal) e' c)

  | .binop_int _ _ _ op l r =>
    let (stmts1, l') ← texpr acc l
    let (stmts2, r') ← texpr stmts1 r
    match binop_op_int op with
    | .inl op' => return (stmts2, .binop op' l' r') -- pure/boolean
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

  | .binop_bool _ _ _ .and l r =>
    -- have : 1 + transSizeTExpr l + max (transSizeTExpr r) 1
        --  < 1 + 1 + transSizeTExpr l + 1 + transSizeTExpr r := by
      -- let r := transSizeTExpr r
      -- have : max r 1 < 1 + 1 + r := by simp [Nat.add_comm]; linarith
      -- linarith
    ternary tau acc l r (.false (by rfl))

  | .binop_bool _ _ _ .or l r  =>
    -- have : 1 + transSizeTExpr l + max 1 (transSizeTExpr r)
        --  < 1 + 1 + transSizeTExpr l + 1 + transSizeTExpr r := by
      -- let r := transSizeTExpr r
      -- have : max 1 r < 1 + 1 + r := by simp [Nat.add_comm]; linarith
      -- linarith
    ternary tau acc l (.true (by rfl)) r

  | .binop_eq _ op _ l r _ _
  | .binop_rel_int _ _ _ op _ l r
  | .binop_rel_char _ _ _ op _ l r =>
    let (stmts1, l') ← texpr acc l
    let (stmts2, r') ← texpr stmts1 r
    return (stmts2, .binop (.comp op) l' r')

  | .ternop _ _ cond tt ff eq => ternary tau acc cond tt ff

  | .app (status := status) f _ τs _ as =>
    let (stmts, args') ← args acc status.type.arity τs as
    let func_lbl ← Env.Func.func f
    let dest ← Env.Func.freshTemp
    let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
    let call := .call ⟨tau, sdest⟩ func_lbl args'
    let size ← Env.Prog.toFunc (Typ.tempSize tau)
    return (call :: stmts, .temp ⟨size, dest⟩)

  | .alloc ty =>
    match ← Env.Prog.toFunc (Typ.size ty) with
    | some size =>
      let dest ← Env.Func.freshTemp
      let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
      return ( .alloc dest (MkTyped.int (.memory size.toNat)) :: acc
             , .temp sdest)
    | none => panic! "IR Trans: Alloc type size not known"

  | .alloc_array _ ty e =>
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

  | .dot _ e field _ _ =>
    let (stmts, address, checks) ← Addr.dot acc e field 0
    let dest ← Env.Func.freshTemp
    let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
    return (.load sdest address :: checks ++ stmts, .temp sdest)

  | .deref _ e =>
    let (stmts, address, checks) ← Addr.deref acc e 0 false
    let dest ← Env.Func.freshTemp
    let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
    return (.load sdest address :: checks ++ stmts, .temp sdest)

  | .index _ _ arr indx =>
    let (stmts, address, checks) ← Addr.index acc arr indx 0
    let dest ← Env.Func.freshTemp
    let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩
    return (.load sdest address :: checks ++ stmts, .temp sdest)

  | .result _
  | .length _ _ =>
    panic! "IR Trans: Dynamically checking contracts are not implemented"


partial def ternary
    (tau : Typ)
    (acc : List IrTree.Stmt)
    (cond : Tst.Expr Δ Γ τ₁)
    (tt : Tst.Expr Δ Γ τ₂)
    (ff : Tst.Expr Δ Γ τ₃)
    : Env.Func ((List IrTree.Stmt) × IrTree.Expr) := do
  let lT ← Env.Func.freshLabel
  let lF ← Env.Func.freshLabel
  let lN ← Env.Func.freshLabel
  let dest ← Env.Func.freshTemp
  let sdest := ⟨← Env.Prog.toFunc (Typ.tempSize tau), dest⟩

  let (stmts, cond') ← texpr acc cond
  let cond_temp ← Env.Func.freshTemp
  let scond_temp := ⟨← Env.Prog.toFunc (Typ.tempSize τ₁), cond_temp⟩
  let condT := .move scond_temp cond'
  let exit := .cjump cond_temp none lT lF
  let curLabel ← Env.Func.curBlockLabel
  let curType ← Env.Func.curBlockType
  let block := ⟨curLabel, curType, (condT :: stmts).reverse, exit⟩
  let () ← Env.Func.addBlock block lT .ternaryTrue

  -- have :=
    -- lt_one_nat_max_left (transSizeTExpr cond)
      -- (transSizeTExpr tt)
      -- (transSizeTExpr ff)
  let (stmtsT, tt') ← texpr [] tt
  let destT := .move sdest tt'
  let exitT := .jump lN
  let curLabel ← Env.Func.curBlockLabel
  let curType ← Env.Func.curBlockType
  let blockT := ⟨curLabel, curType, (destT :: stmtsT).reverse, exitT⟩
  let () ← Env.Func.addBlock blockT lF .ternaryFalse

  -- have :=
    -- lt_one_nat_max_right (transSizeTExpr cond)
      -- (transSizeTExpr tt)
      -- (transSizeTExpr ff)
  let (stmtsF, ff') ← texpr [] ff
  let destF := .move sdest ff'
  let exitF := .jump lN
  let curLabel ← Env.Func.curBlockLabel
  let curType ← Env.Func.curBlockType
  let blockF := ⟨curLabel, curType, (destF :: stmtsF).reverse, exitF⟩
  let () ← Env.Func.addBlock blockF lN .afterTernary

  return ([], .temp sdest)

@[inline] partial def texpr (acc : List IrTree.Stmt) (e : Tst.Expr Δ Γ τ)
    : Env.Func ((List IrTree.Stmt) × Typ.Typed Expr) :=
  MkTyped.expr (expr τ acc e) τ

partial def args
    (acc : List IrTree.Stmt)
    (n : Nat)
    (τs : Fin n → Typ)
    (as : (i : Fin n) → Tst.Expr Δ Γ (τs i))
    : Env.Func ((List IrTree.Stmt) × (List (Typ.Typed Expr))) := do
  match n with
  | .zero => return (acc, [])
  | .succ m =>
    let (stmts, arg') ← texpr acc (as ⟨0, by simp⟩)
    let (stmts', args') ← args stmts m
      (fun i => τs ⟨Nat.succ i, Nat.succ_lt_succ i.isLt⟩)
      (fun i => as ⟨Nat.succ i, Nat.succ_lt_succ i.isLt⟩)
    return (stmts', arg' :: args')


/- returns the elaborated statements, address, and pending memory checks
 - This allows us to maintain the weird semantics for checks
 -/
partial def Addr.addr (tau : Typ) (acc : List IrTree.Stmt)
         (e : Tst.Expr Δ Γ tau)
         (offset : UInt64)
         (check : Bool)
         : Env.Func (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  match e with
  | .dot _ e field _ _ => Addr.dot acc e field offset
  | .deref _ e         => Addr.deref acc e offset check
  | .index _ _ e indx  => Addr.index acc e indx offset
  | _ => panic! s!"IR Trans: Attempted to address a non-pointer {e} {offset}"

partial def Addr.dot (acc : List IrTree.Stmt)
             (texp : Tst.Expr Δ Γ τ)
             (field : Symbol)
             (offset : UInt64)
             : Env.Func
                (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  let structs ← Env.Func.structs
  let struct :=
    match τ with
    | .mem (.struct name) =>
      match structs.find? name with
      | some info => info
      | none => panic! s!"IR Trans: Could not find struct {name}"
    | _ => panic! s!"IR Trans: Expression {texp} does not have struct type"
  let foffset :=
    match struct.fields.find? field with
    | some foffset => foffset
    | none => panic! s!"IR Trans: Could not find field offset {field}"
  Addr.addr τ acc texp (offset + foffset) true

partial def Addr.deref (acc : List IrTree.Stmt)
         (texp : Tst.Expr Δ Γ τ)
         (offset : UInt64)
         (check : Bool)
         : Env.Func (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  let (stmts, texp') ← texpr acc texp
  let address := ⟨texp', offset, none, 0⟩
  if check
  then return (.check (.null texp') :: stmts, address, [])
  else return (stmts, address, [.check (.null texp')])

partial def Addr.index (acc : List IrTree.Stmt)
               (arr : Tst.Expr Δ Γ τ₁)
               (indx : Tst.Expr Δ Γ τ₂)
               (offset : UInt64)
               : Env.Func
                  (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt) := do
  let (stmts1, arr') ← texpr acc arr
  let (stmts2, indx') ← texpr stmts1 indx
  let scale ←
    match τ₁ with
    | .mem (.array tau) => do
      match ← Env.Prog.toFunc (Typ.size tau) with
      | some s => pure s
      | none => panic! "IR Trans: Can't determine array element size"
    | _ => panic! s!"IR Trans: Indexing into non-array type"
  let stmts' :=  .check (.bounds arr' indx') :: .check (.null arr') :: stmts2
  let address := ⟨arr', offset, some indx', scale.toNat⟩
  return (stmts', address, [])
end
-- termination_by
  -- expr tau acc e           => transSizeExpr e
  -- ternary tau acc cc tt ff =>
    -- 1 + transSizeTExpr cc + max (transSizeTExpr tt) (transSizeTExpr ff)
  -- texpr acc te             => transSizeTExpr te
  -- args acc as              => transSizeTExprList as
  -- Addr.addr tau acc e _ _  => 1 + transSizeExpr e
  -- Addr.dot acc e _ _       => 1 + transSizeTExpr e
  -- Addr.deref acc e _ _     => 1 + transSizeTExpr e
  -- Addr.index acc arr i _   => 1 + transSizeTExpr arr + transSizeTExpr i

def Addr.taddr (acc : List IrTree.Stmt)
    : Tst.Expr Δ Γ τ → UInt64 → Bool
    → Env.Func (List IrTree.Stmt × IrTree.Address × List IrTree.Stmt)
  | e => Addr.addr τ acc e

mutual
partial def stmt (past : List IrTree.Stmt) (stm : Tst.Stmt Δ Γ ρ)
    : Env.Func (List IrTree.Stmt) := do
  match stm with
  | .decl _name _ body    => stmts past body.toList
  | .decl_init name init _ _ body =>
    let t ←
      Env.Func.new_var (← Env.Prog.toFunc (Typ.tempSize name.type)) name
    let (istmts, res) ← texpr past init.val
    stmts (.move t res :: istmts) body.toList
  | .assign_var lhs is_var rhs _ =>
    let dest ← Env.Func.var (lhs.get_name is_var)
    let (stms, src) ← texpr past rhs.val
    return .move dest src :: stms

  | .assign (τ₁ := τ₁) tlv _ rhs _ =>
    let lhs' := Elab.lvalue tlv
    let (stms1, dest, checks) ← Addr.taddr past lhs' 0 false
    let (stms2, src) ← texpr stms1 rhs.val
    let _size ← Env.Prog.toFunc (Typ.tempSize τ₁)
    return .store dest src :: checks ++ stms2

  | .asnop (τ₁ := τ₁) (τ₂ := τ₂) _ _ tlv iop rhs =>
    match tlv with
    | .var name _h =>
      let dest ← Env.Func.var name
      let lhs := ⟨τ₁, .temp dest⟩
      let (stms, rhs) ← texpr past rhs.val
      match binop_op_int iop with
      | .inl pure =>
        return .move dest ⟨.prim .int, .binop pure lhs rhs⟩ :: stms
      | .inr impure =>
        let shift := -- include bounds check
          match impure with
          | .lsh | .rsh => [.check (.shift rhs)]
          | .mod => [.check (.mod lhs rhs)]
          | .div => []
        return .effect dest impure lhs rhs :: shift ++ stms
    | _ => /- must be a pointer -/
      let lhs' := Elab.lvalue tlv
      let (stms1, dest, checks) ← Addr.taddr past lhs' 0 false
      let (stms2, src) ← texpr stms1 rhs.val
      let size ← Env.Prog.toFunc (Typ.tempSize τ₁)
      match binop_op_int iop with
      | .inl pure =>
        let temp := ⟨size, ← Env.Func.freshTemp⟩
        let ttemp := ⟨τ₂, .temp temp⟩
        let load := .load temp dest
        let src' := ⟨τ₁, .binop pure ttemp src⟩
        let store := .store dest src'
        return store :: load :: checks ++ stms2
      | .inr impure =>
        let t1 := ⟨size, ← Env.Func.freshTemp⟩
        let t2 := ⟨size, ← Env.Func.freshTemp⟩
        let tt1 := ⟨τ₂, .temp t1⟩
        let tt2 := ⟨τ₂, .temp t2⟩
        let load : IrTree.Stmt := .load t1 dest
        let effect := .effect t2 impure tt1 src
        let store := .store dest tt2
        return store :: effect :: load :: checks ++ stms2

  | .ite (τ := τ) _ cond tt ff =>
    let tLbl  ← Env.Func.freshLabel
    let fLbl  ← Env.Func.freshLabel
    let l_after ← Env.Func.freshLabel

    let (cstms, cond') ← texpr past cond.val
    let cond_temp ← Env.Func.freshTemp
    let scond_temp := ⟨← Env.Prog.toFunc (Typ.tempSize τ), cond_temp⟩
    let condT := .move scond_temp cond'

    let exit := .cjump cond_temp none tLbl fLbl
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, (condT :: cstms).reverse, exit⟩
    let () ← Env.Func.addBlock block tLbl .thenClause

    let tt' ← stmts [] tt.toList
    let exit := .jump l_after
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, tt'.reverse, exit⟩
    let () ← Env.Func.addBlock block fLbl .elseClause

    let ff' ← stmts [] ff.toList
    let exit := .jump l_after
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, ff'.reverse, exit⟩
    let () ← Env.Func.addBlock block l_after .afterITE
    return []

  | .while (τ := τ) _ cond _annos body =>
    let loopGuard ← Env.Func.freshLabel
    let loopBody  ← Env.Func.freshLabel
    let l_afterLoop ← Env.Func.freshLabel

    let exit := .jump loopGuard
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, past.reverse, exit⟩
    let () ← Env.Func.addBlock block loopGuard .loopguard

    let (cstms, cond') ← texpr [] cond.val
    let cond_temp ← Env.Func.freshTemp
    let scond_temp := ⟨← Env.Prog.toFunc (Typ.tempSize τ), cond_temp⟩
    let condT := .move scond_temp cond'

    let exit := .cjump cond_temp (some true) loopBody l_afterLoop
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, (condT :: cstms).reverse, exit⟩
    let () ← Env.Func.addBlock block loopBody .loop

    let body' ← stmts [] body.toList
    let exit := .jump loopGuard
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, body'.reverse, exit⟩
    let () ← Env.Func.addBlock block l_afterLoop .afterLoop
    return []

  | .return_void _ =>
    let exit := .return none
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, past.reverse, exit⟩
    let nextLbl ← Env.Func.freshLabel
    let () ← Env.Func.addBlock block nextLbl .afterRet
    return []

  | .return_tau _ e =>
    let (stms, e') ← texpr past e.val
    let exit := .«return» (some e')
    let curLabel ← Env.Func.curBlockLabel
    let curType ← Env.Func.curBlockType
    let block := ⟨curLabel, curType, stms.reverse, exit⟩
    let nextLbl ← Env.Func.freshLabel
    let () ← Env.Func.addBlock block nextLbl .afterRet
    return []

  | .assert (τ := τ) _ e =>
    if ¬(←Env.Func.unsafe) || (←Env.Func.checkAssertsWhenUnsafe) then
      let l_after ← Env.Func.freshLabel
      let assertLbl := Label.abort

      let (stms, e') ← texpr past e.val
      let cond_temp  ← Env.Func.freshTemp
      let scond_temp := ⟨← Env.Prog.toFunc (Typ.tempSize τ), cond_temp⟩
      let condT := .move scond_temp e'

      let exit := .cjump cond_temp (some true) l_after assertLbl
      let curLabel ← Env.Func.curBlockLabel
      let curType  ← Env.Func.curBlockType
      let block := ⟨curLabel, curType, (condT :: stms).reverse, exit⟩
      let () ← Env.Func.addBlock block l_after curType
      return []
    else return past

  | .error _ e =>
    if ¬(←Env.Func.unsafe) || (←Env.Func.checkAssertsWhenUnsafe) then
      let l_after ← Env.Func.freshLabel

      let (stms, e') ← texpr past e.val
      let exit := .error e'
      let curLabel ← Env.Func.curBlockLabel
      let curType  ← Env.Func.curBlockType
      let block := ⟨curLabel, curType, stms.reverse, exit⟩
      let () ← Env.Func.addBlock block l_after curType
      return []
    else return past

  | .expr e =>
    let (stms, _) ← texpr past e.val -- drop pure expression
    return stms

  | .anno _a =>
    if ← Env.Func.dynCheckContracts
    then panic! "IR Trans: Dynamically checking contracts are not implemented"
    else return past

partial def stmts (past : List IrTree.Stmt)
          (stms : List (Tst.Stmt Δ Γ ρ))
          : Env.Func (List IrTree.Stmt) := do
  match stms with
  | []      => return past
  | s :: ss =>
    let past' ← stmt past s
    stmts past' ss
end
-- termination_by
  -- stmt ctx s   => sizeOf s
  -- stmts ctx ss => sizeOf ss

def dec_args (args : List (Typ.Typed Symbol)) : Env.Prog (List SizedTemp) := do
  match args with
  | [] => return []
  | arg :: args =>
    let size ← Typ.tempSize arg.type
    let t ← Env.Prog.new_var size arg
    let ts ← dec_args args
    return t :: ts

def gdecl (header : Bool) (glbl : Tst.GDecl Δ Δ') : Env.Prog (Option Func) := do
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
      Env.Prog.startFunc entry .funcEntry (stmts [] fdef.body.toList)
    let () ← Env.Prog.addFunc fdef.name label
    let res ← fdef.ret.mapM Typ.tempSize

    if h : Batteries.HashMap.contains blocks entry
    then return some ⟨label, entry, args, blocks, res, h⟩
    else panic! s!"IR Trans: Couldn't find entry block in Std.HashMap"

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
    let offsets := Batteries.HashMap.ofList offsetsR
    let () ← Env.Prog.addStruct sd.name ⟨size', alignment, offsets⟩
    return none

def gdecls (header : Bool)
    (glbls : Tst.GDecl.List Δ Δ')
    : Env.Prog (List Func) := do
  match glbls with
  | .nil => return []
  | .cons gs g =>
    let fs ← gdecls header gs
    let f? ← gdecl header g
    match f? with
    | some f => return f :: fs
    | none   => return fs
  | .update gs => gdecls header gs

def prog (config : Config) (tst : Tst.Prog) : Context IrTree.Prog := do
  let (str_size, str_map) := String.mapping tst.strings
  let initState := Env.Prog.State.new config str_map
  let (hdecs, hstate) ← gdecls true tst.header initState
  let (bdecs, _bstate) ← gdecls false tst.body hstate
  return ⟨(bdecs ++ hdecs).reverse, str_map, str_size⟩
