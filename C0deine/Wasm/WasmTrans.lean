
import C0deine.IrTree.IrTree
import C0deine.Type.Typ
import C0deine.Context.Context
import C0deine.Context.Temp
import C0deine.Context.Label
import C0deine.Config.Config
import C0deine.Utils.Comparison

namespace C0deine.Target.Wasm.Trans

def pure_binop (op : IrTree.PureBinop) : Instr :=
  match op with
  | .add                 => .i32 .add
  | .sub                 => .i32 .sub
  | .mul                 => .i32 .mul
  | .and                 => .i32 .and
  | .xor                 => .i32 .xor
  | .or                  => .i32 .or
  | .comp .less          => .i32 (.lt true)
  | .comp .greater       => .i32 (.gt true)
  | .comp .equal         => .i32 .eq
  | .comp .not_equal     => .i32 .ne
  | .comp .less_equal    => .i32 (.le true)
  | .comp .greater_equal => .i32 (.ge true)

def effect_binop (op : IrTree.EffectBinop) : Instr :=
  match op with
  | .div => .i32 (.div true)
  | .mod => .i32 (.rem true)
  | .lsh => .i32 (.shl)
  | .rsh => .i32 (.shr true)

partial def texpr (te : Typ.Typed IrTree.Expr) : List Instr :=
  match te.data with
  | .byte b       => [.i32 (.const b.toNat)]
  | .const i      => [.i32 (.const i)]
  | .temp t       => [.wasm_local (.get (.temp t.temp))]
  | .memory m     => [.i64 (.const m)]
  | .binop op l r =>
    let l' := texpr l
    let r' := texpr r
    let op' := pure_binop op
    l'.append r' |>.append [op']

def expr (e : IrTree.Expr) : List Instr := texpr ⟨Typ.any, e⟩

def check (check : IrTree.Check) : List Instr :=
  match check with
  | .null te =>
    let te' := texpr te
    let comment := .comment s!"Null check on {te}"
    let block := .block none <| te'.append
      [ .br_if (.num 0)
      , .call Label.abort -- todo maybe we need to pass args?
      , .unreachable
      ]
    [comment, block]

  | .shift te =>
    let te' := texpr te
    let comment := .comment s!"Shift check on {te}"
    let block := .block none [.block none <| te'.append
      [ .wasm_local (.tee (.temp Temp.general))
      , .i32 (.const 0)
      , .i32 (.lt true)         -- 0 > te
      , .br_if (.num 0)         -- abort
      , .wasm_local (.get (.temp Temp.general))
      , .i32 (.const 31)
      , .i32 (.gt true)         -- 31 < te
      , .br_if (.num 0)         -- abort
      , .br (.num 1)            -- success
      ], .call Label.abort, .unreachable] -- todo maybe we need to pass args?
    [comment, block]

  | .bounds source index =>
    -- null check already handled, need to check length
    let source' := texpr source
    let index' := texpr index
    let comment := .comment s!"Bounds check on {check}"
    let block := .block none [.block none <| index'.append
      [ .wasm_local (.tee (.temp Temp.index))
      , .i32 (.const 0)
      , .i32 (.lt true)         -- 0 > te
      , .br_if (.num 0)         -- abort
      ] |>.append source' |>.append
      [ .wasm_local (.tee (.temp Temp.general))
      , .i32 (.const (-8))
      , .i32 .add               -- &length(arr)
      , .i32 .load
      , .wasm_local (.get (.temp Temp.index))
      , .i32 (.le true)         -- index >= length(arr)
      , .br_if (.num 0)         -- abort
      , .br (.num 1)            -- success
      ], .call Label.abort, .unreachable] -- todo maybe we need to pass args?
    [comment, block]

def addr (a : IrTree.Address) : List Instr :=
  let base' := texpr a.base
  let offset' := [.i64_extend_i32_u, .i64 (.const a.offset.toNat), .i64 .add]
  base'.append offset' |>.append (
    match a.index with
    | .some index =>
      let index' := texpr index
      index'.append [.i64_extend_i32_u, .i64 (.const a.scale), .i64 .mul, .i64 .add]
    | .none => []
  )

def stmt : IrTree.Stmt → List Instr
  | .move dest te =>
    let te' := texpr te
    te'.append [.wasm_local (.set (.temp dest.temp))]

  | .effect dest op lhs rhs =>
    let lhs' := texpr lhs
    let rhs' := texpr rhs
    let op'  := effect_binop op
    lhs'.append rhs' |> .append [op', .wasm_local (.set (.temp dest.temp))]

  | .call dest name args    =>
    let args' := args.map texpr
    args'.join |>.append [.call name, .wasm_local (.set (.temp dest.temp))]

  | .alloc dest size        =>
    let size' := texpr size
    size'.append
      [ .i64_extend_i32_u
      , .i64 (.const 0)
      , .i64 .load          -- 0 address has ptr to next free segment
      , .i64 .add           -- get next free pointer after alloc
      , .wasm_local (.set (.temp Temp.general))
      , .block .none [      -- loop to increase memory size
        .loop .none
        [ .wasm_local (.get (.temp Temp.general))
        , .mem_size         -- returns number of pages
        , .i64 (.const 65536)
        , .i64 .mul
        , .i64 (.lt false)
        , .br_if (.num 1)   -- next ptr within bounds, don't grow
        , .i64 (.const 1)   -- grow by 1 page
        , .mem_grow
        , .br (.num 0)
        ]]
      , .i64 (.const 0)
      , .i64 .load          -- pointer we want to return
      , .wasm_local (.set (.temp dest))
      , .i64 (.const 0)
      , .wasm_local (.get (.temp Temp.general))
      , .i64 .store         -- update free pointer
      ]

  | .load dest a            =>
    let addr' := addr a
    let load' :=
      match dest.size with
      | .byte   => .i64 (.load8 false)
      | .word   => .i64 (.load16 false)
      | .double => .i64 (.load32 false)
      | .quad   => .i64 .load
    addr'.append [load', .wasm_local (.set (.temp dest.data))]

  | .store a source         =>
    let source' := texpr source
    let addr' := addr a
    let store' :=
      match source.type with
      | .any      => .i64 .store
      | (.mem _)  => .i64 .store
      | (.prim .bool) => .i64 .store8
      | (.prim .int) => .i64 .store32
    addr'.append [.i32_wrap_i64] |>.append source' |>.append [store']

  | .check ch               => check ch

structure TransBlockData where
  instrs : List Instr
  visited : List Label

def block
    (f : IrTree.Func)
    (b : IrTree.Block)
    (loop_exit : Label)
    (visited : List Label)
    : Context TransBlockData :=
  sorry
