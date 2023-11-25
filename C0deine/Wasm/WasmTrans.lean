
import C0deine.IrTree.IrTree
import C0deine.Type.Typ
import C0deine.Context.Context
import C0deine.Context.Temp
import C0deine.Context.Label
import C0deine.Config.Config
import C0deine.Utils.Comparison
import C0deine.ControlFlow.Relooper
import C0deine.Wasm.Wasm

namespace C0deine.Target.Wasm.Trans

open Numbers Wasm.Text Wasm.Text.Instr Wasm.Syntax.Instr.Numeric
  Wasm.Syntax.Instr.Memory

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
  | .mod => i32_bin (.rem .s)
  | .lsh => i32_bin (.shl)
  | .rsh => i32_bin (.shr .s)

partial def texpr (te : Typ.Typed IrTree.Expr) : List Instr :=
  match te.data with
  | .byte b       => [i32_const (Unsigned.ofNat b.toNat)]
  | .const i      => [i32_const (Signed.ofInt i)]
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
    te' ++ [locl (.set (stemp dest))]

  | .effect dest op lhs rhs =>
    let lhs' := texpr lhs
    let rhs' := texpr rhs
    let op'  := effect_binop op
    lhs' ++ rhs' ++ [op', locl (.set (stemp dest))]

  | .call dest name args    =>
    let args' := args.map texpr
    args'.join.append [Plain.call (label name), locl (.set (stemp dest))]

  | .alloc dest asize        =>
    let size' := texpr asize
    size' ++
      [.plain <|.call (label Label.calloc), locl (.set (stemp ⟨.quad, dest⟩))]

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
    addr' ++ [load', locl (.set (stemp dest))]

  | .store a source         =>
    let source' := texpr source
    let addr'   := addr a
    let store'  := i32_mem (.store ⟨0, 4⟩)
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
  | .cjump t hotpath tt ff => []
  | .return .none => [Plain.wasm_return]
  | .return (.some te) => texpr te |>.append [Plain.wasm_return]

-- todo clean this up with helpers and such!
def func_body
    (f : IrTree.Func)
    (shape : ControlFlow.Relooper.Shape)
    : List Instr :=
  (traverse shape .none).fst ++ [.plain .unreachable]
where
  error (msg : String) : List Instr × Option IrTree.BlockExit :=
      ([.comment msg], .none)
  traverse (shape : ControlFlow.Relooper.Shape)
           (priorExit : Option IrTree.BlockExit)
           : List Instr × Option IrTree.BlockExit :=
  match shape with
  | .simple l next =>
    match f.blocks.find? l with
    | .some block =>
      let body_instr := block.body.bind stmt
      let exit_instr := exit block.exit
      let (next_instr, next_exit) :=
        match next with
        | .some n => traverse n (.some block.exit)
        | .none   => ([], .none)

      ( body_instr ++ exit_instr ++ next_instr
      , match next_exit with | .none => .some block.exit | _ => next_exit
      )
    | .none =>
      error s!"WASM Trans: Could not find block labeled {l}, in shape {shape} in {f}!"
  | .loop inner next =>
    let lbls := ControlFlow.Relooper.Shape.getLabels shape
    match inner, lbls with
    | .some i, [i_lbl] =>
      let (i_instr, body_exit) := traverse i .none
      let (n_instr, next_exit) :=
        match next with
        | .some n => traverse n body_exit
        | .none   => ([], .none)

      match body_exit with
      | .some (.cjump t _ _ _) =>
        ( loop (.name i_lbl.toWasmIdent)
            ( i_instr
              ++ [locl (.get (temp t)), plain <|.br_if (label i_lbl)]
            ) :: n_instr
        , next_exit
        )
      | _ =>
        error s!"WASM Trans Error: Shape loop, {shape}, body has improper exit {body_exit}!"
    | .some _, _ =>
      error s!"WASM Trans: Shape loop, {shape}, has too many/few successors: {lbls}!"
    | .none, _ =>
      error s!"WASM Trans: Shape loop, {shape}, missing loop body!"
  | .multi left right next =>
    let lbls := ControlFlow.Relooper.Shape.getLabels shape
    match left, right, lbls, priorExit with
    | .some l, .some r, [l_lbl, r_lbl], .some (.cjump ct _hotpath tt ff) =>
      let c_flip := if ff = l_lbl then [i32_eqz] else []
      let (l_instr, l_exit) := traverse l .none
      let (r_instr, r_exit) := traverse r .none
      let (n_instr, next_exit) :=
        match next with -- l_exit == r_exit
        | .some n => traverse n r_exit
        | .none   => ([], .none)

      let cond :=
        [locl (.get (temp ct))]
        ++ c_flip
        ++ [.plain <|.br_if (label r_lbl)]
      let r_block := Instr.block <|
        .block (.name r_lbl.toWasmIdent)
          (.typeuse (.elab_param_res [] []))
          (cond ++ r_instr ++ [.plain <|.br (label l_lbl)])
          .none
      let l_block := Instr.block <|
        .block (.name l_lbl.toWasmIdent)
          (.typeuse (.elab_param_res [] []))
          (r_block :: l_instr)
          .none

      (l_block :: n_instr, next_exit)
    | _, _, _, .some (.cjump _ _ _ _) =>
      error s!"WASM Trans: Shape multi, {shape}, missing branch!"
    | _, _, _, .none | _, _, _, .some _ =>
      error s!"WASM Trans: Shape multi, {shape}, doesn't have condition to branch: {priorExit}!"
  | .illegal lbls => error s!"WASM Trans: Illegal shape {shape}!"


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

def func (f : IrTree.Func) (shape : ControlFlow.Relooper.Shape) : Module.Function :=
  let body := func_body f shape

  let params : List Wasm.Text.Typ.Param :=
    f.args.map (fun st => (.some st.temp.toWasmIdent, .num .i32))
  let result : List Wasm.Text.Typ.Result :=
    f.result_size.map (fun _ => [.num .i32]) |>.getD []

  let locals : List Wasm.Text.Module.Local :=
    let args := f.args.map (·.data.toWasmIdent)
    (find_used_temps body).filterMap (fun id =>
      if args.elem id then .none else .some ⟨.some id, .num .i32⟩
    )

  { lbl     := .some f.name.toWasmIdent
  , typeuse := .elab_param_res params result
  , locals  := locals
  , body    := body
  }

def prog (prog : IrTree.Prog)
         (shapes : List (ControlFlow.Relooper.Shape))
         : List Module.Function :=
  List.zip prog shapes |>.map (fun (f, s) => func f s)
