
import C0deine.IrTree.IrTree
import C0deine.Type.Typ
import C0deine.Context.Context
import C0deine.Context.Temp
import C0deine.Context.Label
import C0deine.Config.Config
import C0deine.Utils.Comparison
import C0deine.ControlFlow.Relooper
import Wasm.Text.Instr
import Wasm.Text.Index
import Wasm.Text.Module

namespace C0deine.Wasm.Trans

open Numbers
open Wasm.Text
open Wasm.Text.Instr
open Wasm.Syntax.Instr.Numeric
open Wasm.Syntax.Instr.Memory

def i_eqz (nn : Size) : Wasm.Syntax.Instr.Numeric nn :=
  Wasm.Syntax.Instr.Numeric.integer (Integer.test (nn := nn) .eqz)
def i_const (nn : Size)
    : Numbers.Unsigned nn.toBits → Wasm.Syntax.Instr.Numeric nn :=
  Wasm.Syntax.Instr.Numeric.integer ∘ Integer.const
def i_un (nn : Size) : Integer.Unop → Wasm.Syntax.Instr.Numeric nn :=
  Wasm.Syntax.Instr.Numeric.integer ∘ Integer.unop (nn := nn)
def i_bin (nn : Size) : Integer.Binop → Wasm.Syntax.Instr.Numeric nn :=
  Wasm.Syntax.Instr.Numeric.integer ∘ Integer.binop (nn := nn)
def i_rel (nn : Size) : Integer.Relation → Wasm.Syntax.Instr.Numeric nn :=
  Wasm.Syntax.Instr.Numeric.integer ∘ Integer.relation (nn := nn)

def i32_mem : Wasm.Syntax.Instr.Memory.Integer .double → Instr :=
  Instr.plain ∘ Instr.Plain.memory ∘ Instr.Memory.integer
def i64_mem : Wasm.Syntax.Instr.Memory.Integer .quad → Instr :=
  Instr.plain ∘ Instr.Plain.memory ∘ Instr.Memory.integer

def num_to_instr : Wasm.Syntax.Instr.Numeric nn → Instr :=
  Instr.plain ∘ Instr.Plain.numeric

def i32_eqz   : Instr                    := num_to_instr (i_eqz .double)
def i32_un    : Integer.Unop     → Instr := num_to_instr ∘ i_un .double
def i32_bin   : Integer.Binop    → Instr := num_to_instr ∘ i_bin .double
def i32_rel   : Integer.Relation → Instr := num_to_instr ∘ i_rel .double
def i32_const : Unsigned32       → Instr := num_to_instr ∘ i_const .double

def i64_const : Unsigned64       → Instr := num_to_instr ∘ i_const .quad
def i64_bin   : Integer.Binop    → Instr := num_to_instr ∘ i_bin .quad
def i64_rel   : Integer.Relation → Instr := num_to_instr ∘ i_rel .quad

def locl  : Instr.Local → Instr := .plain ∘ .locl
def globl : Instr.Local → Instr := .plain ∘ .locl
def block (l : Wasm.Text.Label) (ins : List Instr) : Instr :=
  .block (.block l (.value .none) ins .none)
def loop (l : Wasm.Text.Label) (ins : List Instr) : Instr :=
  .block (.loop l (.value .none) ins .none)

def temp  : Temp      → Module.Index := .name ∘ Temp.toWasmIdent
def stemp : SizedTemp → Module.Index := .name ∘ SizedTemp.toWasmIdent
def label : Label     → Module.Index := .name ∘ Label.toWasmIdent

def pure_binop (op : IrTree.PureBinop) : Instr :=
  match op with
  | .add                 => i32_bin .add
  | .sub                 => i32_bin .sub
  | .mul                 => i32_bin .mul
  | .and                 => i32_bin .and
  | .xor                 => i32_bin .xor
  | .or                  => i32_bin .or
  | .comp .less          => i32_rel (.lt .s)
  | .comp .greater       => i32_rel (.gt .s)
  | .comp .equal         => i32_rel .eq
  | .comp .not_equal     => i32_rel .ne
  | .comp .less_equal    => i32_rel (.le .s)
  | .comp .greater_equal => i32_rel (.ge .s)

def effect_binop (op : IrTree.EffectBinop) : Instr :=
  match op with
  | .div => i32_bin (.div .s)
  | .mod => i32_bin (.mod .s)
  | .lsh => i32_bin (.shl)
  | .rsh => i32_bin (.shr .s)

partial def texpr (te : Typ.Typed IrTree.Expr) : List Instr :=
  match te.data with
  | .byte b       => [i32_const (Unsigned.ofNat b.toNat)]
  | .const i      => [i32_const (Unsigned.ofInt i)]
  | .temp t       => [locl (.get (stemp t))]
  | .memory m     => [i32_const (Unsigned.ofNat m)]
  | .binop op l r =>
    let l' := texpr l
    let r' := texpr r
    let op' := pure_binop op
    l'.append r' |>.append [op']
  | .and l r =>
    let l' := texpr l
    let r' := texpr r
    l'.append [block .no_label (
      [ i32_eqz
      , Plain.br_if (.num 0) -- short-circuit if false
      ] |>.append r'
    )]
  | .or l r =>
    let l' := texpr l
    let r' := texpr r
    l'.append [block .no_label (
      [ .plain <|.br_if (.num 0) -- short-circuit if true
      ] |>.append r'
    )]

def expr (e : IrTree.Expr) : List Instr := texpr ⟨Typ.any, e⟩

def check (check : IrTree.Check) : List Instr :=
  match check with
  | .null te =>
    let te' := texpr te
    let comment := .comment s!"Null check on {te}"
    let block := block .no_label <| te'.append
      [ Plain.br_if (.num 0)
      , Plain.call (label Label.abort) -- todo maybe we need to pass args?
      , Plain.unreachable
      ]
    [comment, block]

  | .shift te =>
    let te' := texpr te
    let comment := .comment s!"Shift check on {te}"
    let block := block .no_label
      [ block .no_label <| te'.append
        [ locl (.tee (temp Temp.general))
        , i32_const 0
        , i32_rel (.lt .s)            -- 0 > te
        , Plain.br_if (.num 0)        -- abort
        , locl (.get (temp Temp.general))
        , i32_const 31
        , i32_rel (.gt .s)            -- 31 < te
        , Plain.br_if (.num 0)        -- abort
        , Plain.br (.num 1)           -- success
        ]
      , Plain.call (label Label.abort)
      , Plain.unreachable
      ] -- todo maybe we need to pass args?
    [comment, block]

  | .bounds source index =>
    -- null check already handled, need to check length
    let source' := texpr source
    let index' := texpr index
    let comment := .comment s!"Bounds check on {check}"
    let block := block .no_label
      [ block .no_label <| index'.append
        [ locl (.tee (temp Temp.index))
        , i32_const 0
        , i32_rel (.lt .s)             -- 0 > te
        , Plain.br_if (.num 0)         -- abort
        ] |>.append source' |>.append
        [ locl (.tee (temp Temp.general))
        , i32_const (-8)
        , i32_bin .add                 -- &length(arr)
        , i32_mem (.load ⟨0, 4⟩)
        , locl (.get (temp Temp.index))
        , i32_rel (.le .s)             -- index >= length(arr)
        , Plain.br_if (.num 0)         -- abort
        , Plain.br (.num 1)            -- success
        ]
      , Plain.call (label Label.abort)
      , Plain.unreachable
      ] -- todo maybe we need to pass args?
    [comment, block]

def addr (a : IrTree.Address) : List Instr :=
  let base' := texpr a.base
  let offset' :=
    [ i32_const (Unsigned.ofNat a.offset.toNat)
    , i32_bin .add
    ]
  base'.append offset' |>.append (
    match a.index with
    | .some index =>
      let index' := texpr index
      index'.append
        [ i32_const (Unsigned.ofNat a.scale)
        , i32_bin .mul
        , i32_bin .add
        ]
    | .none => []
  )

def stmt : IrTree.Stmt → List Instr
  | .move dest te =>
    let te' := texpr te
    te'.append [locl (.set (stemp dest))]

  | .effect dest op lhs rhs =>
    let lhs' := texpr lhs
    let rhs' := texpr rhs
    let op'  := effect_binop op
    lhs'.append rhs' |> .append [op', locl (.set (stemp dest))]

  | .call dest name args    =>
    let args' := args.map texpr
    args'.join.append [Plain.call (label name), locl (.set (stemp dest))]

  | .alloc dest asize        =>
    let size' := texpr asize
    size'.append
      [ i32_const 0
      , i32_mem (.load ⟨0, 4⟩)          -- 0 address has ptr to next free seg
      , i32_bin .add                    -- get next free pointer after alloc
      , locl (.set (temp Temp.general))
      , block .no_label
        [ loop .no_label                -- loop to increase memory size
          [ locl (.get (temp Temp.general))
          , Plain.memory .size          -- returns number of pages
          , i32_const 65536
          , i32_bin .mul
          , i32_rel (.lt .u)
          , Plain.br_if (.num 1)        -- next ptr within bounds, don't grow
          , i32_const 1                 -- grow by 1 page
          , Plain.memory .grow
          , Plain.br (.num 0)
          ]
        ]
      , i32_const 0
      , i32_mem (.load ⟨0, 4⟩)          -- pointer we want to return
      , locl (.set (temp dest))
      , i32_const 0
      , locl (.get (temp Temp.general))
      , i32_mem (.store ⟨0, 4⟩)         -- update free pointer
      ]

  | .load dest a            =>
    let addr' := addr a
    let load' :=
      i32_mem (.load ⟨0, 4⟩)
      -- match dest.size with
      -- | .byte   =>
        -- i64_mem (.load8 .u ⟨0, Unsigned.ofNat dest.size.bytes⟩)
      -- | .word   => i64_mem (.load16 .u ⟨0, Unsigned.ofNat dest.size.bytes⟩)
      -- | .double => i64_mem (.load32 .u ⟨0, Unsigned.ofNat dest.size.bytes⟩)
      -- | .quad   => i64_mem (.load ⟨0, Unsigned.ofNat dest.size.bytes⟩)
    addr'.append [load', locl (.set (stemp dest))]

  | .store a source         =>
    let source' := texpr source
    let addr' := addr a
    let store' :=
      i32_mem (.store ⟨0, 4⟩)
      -- match source.type with
      -- | .any | (.mem _) =>
        -- i64_mem (.store ⟨0, Unsigned.ofNat source.type.sizeof!⟩)
      -- | (.prim .bool) =>
        -- i64_mem (.store8 ⟨0, Unsigned.ofNat source.type.sizeof!⟩)
      -- | (.prim .int)   =>
        -- i64_mem (.store32 ⟨0, Unsigned.ofNat source.type.sizeof!⟩)

    addr' ++ source' ++ [store']

  | .check ch               => check ch

@[inline] def exit (bexit : IrTree.BlockExit) : List Instr :=
  match bexit with
  | .jump l => []
  | .cjump te hotpath tt ff => texpr te
  | .return .none => [Plain.wasm_return]
  | .return (.some te) => texpr te |>.append [Plain.wasm_return]

-- todo clean this up with helpers and such!
def func_body
    (f : IrTree.Func)
    (shape : ControlFlow.Relooper.Shape)
    : List Instr :=
  traverse shape .none ++ [.plain .unreachable]
where traverse (shape : ControlFlow.Relooper.Shape)
               (priorExit : Option IrTree.BlockExit) :=
  match shape with
  | .simple l next =>
    match f.blocks.find? l with
    | .some block =>
      let body_instr := block.body.bind stmt
      let exit_instr := exit block.exit
      let next_instr :=
        match next with
        | .some n => traverse n (.some block.exit)
        | .none   => []

      body_instr ++ exit_instr ++ next_instr
    | .none =>
      panic! s!"WASM Trans: Could not find block labeled {l}, in shape {shape} in {f}!"
  | .loop inner next =>
    let lbls := ControlFlow.Relooper.Shape.getLabels shape
    match inner, lbls with
    | .some i, [i_lbl] =>
      let i_instr := traverse i .none
      let n_instr :=
        match next with
        | .some n => traverse n .none
        | .none   => []

      loop (.name i_lbl.toWasmIdent)
        ( i_instr ++ [plain <|.br_if (label i_lbl)]
        ) :: n_instr
    | .some _, _ =>
      panic! s!"WASM Trans: Shape loop, {shape}, has too many/few successors: {lbls}!"
    | .none, _ =>
      panic! s!"WASM Trans: Shape loop, {shape}, missing loop body!"
  | .multi left right next =>
    let lbls := ControlFlow.Relooper.Shape.getLabels shape
    match left, right, lbls, priorExit with
    | .some l, .some r, [l_lbl, r_lbl], .some (.cjump cc _hotpath tt ff) =>
      let c_flip := if ff = l_lbl then [i32_eqz] else []
      let l_instr := traverse l .none
      let r_instr := traverse r .none
      let n_instr :=
        match next with
        | .some n => traverse n .none
        | .none   => []

      let cond := c_flip ++ [.plain <|.br_if (label r_lbl)]
      let r_block := Instr.block <|
        .block (.name r_lbl.toWasmIdent)
          (.typeuse (.elab_param_res [⟨.none, .num .i32⟩] []))
          (cond ++ r_instr ++ [.plain <|.br (label l_lbl)])
          .none
      let l_block := Instr.block <|
        .block (.name l_lbl.toWasmIdent)
          (.typeuse (.elab_param_res [⟨.none, .num .i32⟩] []))
          (r_block :: l_instr)
          .none

      l_block :: n_instr
    | _, _, _, .some (.cjump _ _ _ _) =>
      panic! s!"WASM Trans: Shape multi, {shape}, missing branch!"
    | _, _, _, .none | _, _, _, .some _ =>
      panic! s!"WASM Trans: Shape multi, {shape}, doesn't have condition to branch {priorExit}!"
  | .illegal lbls => panic! s!"WASM Trans: Illegal shape {shape}!"

-- todo: temp just to get things working
partial def find_used_temps (instrs : List Instr) : List Ident :=
  instrs.foldl (fun acc i =>
    match i with
    | .block (.block _ _ body _)       => find_used_temps body ++ acc
    | .block (.loop _ _ body _)        => find_used_temps body ++ acc
    | .plain (.locl (.get (.name t)))  => t :: acc
    | .plain (.locl (.set (.name t)))  => t :: acc
    | .plain (.locl (.tee (.name t)))  => t :: acc
    | .plain (.globl (.get (.name t))) => t :: acc
    | .plain (.globl (.set (.name t))) => t :: acc
    | _ => acc
  ) [] |>.eraseDups

def wasm_val_type_from_temp_ident (id : Ident) : Wasm.Syntax.Typ.Val :=
  ValueSize.double.wasm_val_type
  -- if id.name.startsWith "tq"      then ValueSize.quad.wasm_val_type
  -- else if id.name.startsWith "tl" then ValueSize.double.wasm_val_type
  -- else if id.name.startsWith "tw" then ValueSize.word.wasm_val_type
  -- else if id.name.startsWith "tb" then ValueSize.byte.wasm_val_type
  -- else ValueSize.double.wasm_val_type

def func (f : IrTree.Func) (shape : ControlFlow.Relooper.Shape) : Module.Function :=
  let body := func_body f shape

  let params : List Wasm.Text.Typ.Param :=
    f.args.map (fun st => (.some st.temp.toWasmIdent, st.size.wasm_val_type))
  let result : List Wasm.Text.Typ.Result :=
    f.result_size.map ([·.wasm_val_type]) |>.getD []

  let locals : List Wasm.Text.Module.Local :=
    (find_used_temps body).map (fun id =>
      let type := wasm_val_type_from_temp_ident id
      ⟨.some id, type⟩
    )

  { lbl     := .some f.name.toWasmIdent
  , typeuse := .elab_param_res params result
  , locals  := locals
  , body    := body
  }

def prog (prog : IrTree.Prog)
         (shapes : List (ControlFlow.Relooper.Shape))
         : Module :=
  let log_id : Ident := ⟨"log", sorry, sorry⟩
  let log : Module.Field := .imports
    ⟨ "console"
    , "log"
    , .func (.some log_id) (.elab_param_res [(.none, .num .i32)] [])
    ⟩

  let abort : Module.Field := .funcs
    { lbl     := .some Label.abort.toWasmIdent
    , typeuse := .elab_param_res [] []
    , locals  := []
    , body    :=
      [ i32_const (-1)
      , Plain.call (.name log_id)
      , Plain.unreachable
      ]
    }

  let main : Module.Field := .funcs
    { lbl     := .some Label.main.toWasmIdent
    , typeuse := .elab_param_res [] []
    , locals  := []
    , body    :=
      [ Plain.call (.name ⟨"_c0_main", sorry, sorry⟩)
      , Plain.call (.name log_id)
      ]
    }

  let memory : Module.Field := .mems ⟨.none, ⟨1, .none⟩⟩
  let start : Module.Field := .start ⟨.name Label.main.toWasmIdent⟩

  let funcs : List Module.Field :=
    List.zip prog shapes |>.map (fun (f, s) => .funcs (func f s))

  ⟨.none, [log, abort, memory, main, start] ++ funcs⟩
