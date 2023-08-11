
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

def texpr : IrTree.TypedExpr → List Instr
  | .typed _type e =>
    match e with
    | .byte b       => [.i32 (.const b.toNat)]
    | .const i      => [.i32 (.const i)]
    | .temp t       => [.wasm_local (.get (.temp t.temp))]
    | .memory m     => [.i64 (.const m)]
    | .binop op l r =>
      let l' := texpr l
      let r' := texpr r
      let op' := pure_binop op
      l'.append r' |>.append [op']

def expr (e : IrTree.Expr) : List Instr :=
  texpr (.typed Typ.any e)

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
    let pointer : List Instr :=
      [ .i32 (.const 0)
      , .wasm_local (.tee (.temp Temp.general))
      ]
    let size' := texpr size
    let alloc := size'.append
      [ .wasm_local (.tee (.temp Temp.general))
      , .loop none
        [ sorry
        ]
      ]

    sorry
  | .load dest addr         => sorry
  | .store addr source      => sorry
  | .check ch               => check ch


#eval s!"(local $%t0 i32)\n{check (.shift (.typed .any (.const 5)))}"
