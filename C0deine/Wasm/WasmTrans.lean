/- C0deine - WasmTrans
   Translates the IR Tree (quad assembly) into the WASM CST. For now, WASM is
   32-bit, so some of our size annotations are ignored for now (although this
   will be changed when/if wasm64 is made standard).
   - Thea Brick
 -/
import C0deine.IrTree.IrTree
import C0deine.Type.Typ
import C0deine.Context.Context
import C0deine.Context.Temp
import C0deine.Context.Label
import C0deine.Config.Config
import C0deine.Utils.Comparison
import C0deine.ControlFlow.Relooper
import C0deine.Wasm.Wasm
import Wasm.Notation

namespace C0deine.Target.Wasm.Trans

open Numbers Wasm.Text Wasm.Text.Instr Wasm.Syntax.Instr.Numeric
  Wasm.Syntax.Instr.Memory

open Wasm.Text.Notation in
def pure_binop (op : IrTree.PureBinop) : Instr :=
  match op with
  | .add                 => [wat_instr| i32.add ]
  | .sub                 => [wat_instr| i32.sub ]
  | .mul                 => [wat_instr| i32.mul ]
  | .and                 => [wat_instr| i32.and ]
  | .xor                 => [wat_instr| i32.xor ]
  | .or                  => [wat_instr| i32.or  ]
  | .comp .less          => [wat_instr| i32.lt_s]
  | .comp .greater       => [wat_instr| i32.gt_s]
  | .comp .equal         => [wat_instr| i32.eq  ]
  | .comp .not_equal     => [wat_instr| i32.ne  ]
  | .comp .less_equal    => [wat_instr| i32.le_s]
  | .comp .greater_equal => [wat_instr| i32.ge_s]

open Wasm.Text.Notation in
def effect_binop (op : IrTree.EffectBinop) : Instr :=
  match op with
  | .div => [wat_instr| i32.div_s]
  | .mod => [wat_instr| i32.rem_s]
  | .lsh => [wat_instr| i32.shl  ]
  | .rsh => [wat_instr| i32.shr_s]

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
      , Plain.br_if 0 -- short-circuit if false
      ] |>.append r'
    )]
  | .or l r =>
    let l' := texpr l
    let r' := texpr r
    l'.append [block .no_label (
      [ .plain <|.br_if 0 -- short-circuit if true
      ] |>.append r'
    )]

def expr (e : IrTree.Expr) : List Instr := texpr ⟨Typ.any, e⟩

def check (check : IrTree.Check) : List Instr :=
  match check with
  | .null te =>
    let te' := texpr te
    let comment := .comment s!"Null check on {te}"
    let block := block .no_label <| te'.append
      [ Plain.br_if 0
      , Error.mem
      , Plain.call (label Label.abort)
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
        , Plain.br_if 0        -- abort
        , locl (.get (temp Temp.general))
        , i32_const 31
        , i32_rel (.gt .s)            -- 31 < te
        , Plain.br_if 0        -- abort
        , Plain.br 1           -- success
        ]
      , Error.arith
      , Plain.call (label Label.abort)
      , Plain.unreachable
      ]
    [comment, block]

  | .mod l r =>
    let l' := texpr l
    let r' := texpr r
    let comment := .comment s!"Mod check on {l} % {r}"
    let block := block .no_label <| (l'.append r').append
      [ i32_const (-1)
      , i32_rel .ne
      , Plain.br_if 0
      , i32_const Signed.MIN_VALUE
      , i32_rel .ne
      , Plain.br_if 0
      , Error.arith
      , Plain.call (label Label.abort)
      , Plain.unreachable
      ]
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
        , Plain.br_if 0         -- abort
        ] |>.append source' |>.append
        [ locl (.tee (temp Temp.general))
        , i32_const (-8)
        , i32_bin .add                 -- &length(arr)
        , i32_mem (.load ⟨0, 0⟩)
        , locl (.get (temp Temp.index))
        , i32_rel (.le .s)             -- index >= length(arr)
        , Plain.br_if 0         -- abort
        , Plain.br 1            -- success
        ]
      , Error.mem
      , Plain.call (label Label.abort)
      , Plain.unreachable
      ]
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
    args'.join.append [Plain.call (label name)] ++ (
      if let .any := dest.type then []
      else [locl (.set (stemp dest.data))]
    )

  | .alloc dest asize        =>
    let size' := texpr asize
    size' ++
      [.plain <|.call (label Label.calloc), locl (.set (stemp ⟨.quad, dest⟩))]

  | .load dest a            =>
    let addr' := addr a
    let load' :=
      match dest.size with
      | .byte   => i32_mem (.load8 .u ⟨0, 0⟩)
      | .word   => i32_mem (.load16 .u ⟨0, 0⟩)
      | .double => i32_mem (.load ⟨0, 0⟩)  -- 64bit pointers are unrepresentable
      | .quad   => i32_mem (.load ⟨0, 0⟩)  -- so make them 32
    addr' ++ [load', locl (.set (stemp dest))]

  | .store a source         =>
    let source' := texpr source
    let addr'   := addr a
    let store'  :=
      match source.type with
      | .any | (.mem _) | (.prim .string) =>
        i32_mem (.store ⟨0, 0⟩)
      | (.prim .bool) | (.prim .char) =>
        i32_mem (.store8 ⟨0, 0⟩)
      | (.prim .int) =>
        i32_mem (.store ⟨0, 0⟩)
    addr' ++ source' ++ [store']

  | .copy dest src len      =>
    let dest' := addr dest
    let src'  := addr src
    let len'  := i32_const (Unsigned.ofNat len)
    dest' ++ src' ++ [len', Plain.memory .copy]

  | .check ch               => check ch


/- Converting shapes into WASM -/
@[inline] def exit (bexit : IrTree.BlockExit)
                   (loopBreak : Label → Option Label) : List Instr :=
  match bexit with
  | .jump l =>
    if let some lb := loopBreak l
    then [Plain.br lb.toWasmLoopBreak]
    else []
  | .cjump t _hotpath tt ff =>
    if let some lb := loopBreak tt
    then [locl (.get (temp t)), Plain.br_if lb.toWasmLoopBreak]
    else if let some lb := loopBreak ff
    then [locl (.get (temp t)), i32_eqz, Plain.br_if lb.toWasmLoopBreak]
    else []
  | .return .none => [Plain.wasm_return]
  | .return (.some te) => texpr te |>.append [Plain.wasm_return]
  | .error te =>
    texpr te |>.append [Plain.call (label Label.error), Plain.unreachable]

partial def find_cjump
    (f : IrTree.Func) : Option IrTree.BlockExit → Option (Temp × Label × Label)
  | .none => .none
  | .some (.jump l) => find_cjump f (f.blocks.find? l |>.map (·.exit))
  | .some (.cjump t _ tt ff) => .some (t, tt, ff)
  | _ => .none

partial def func_body
    (f : IrTree.Func)
    (shape : ControlFlow.Relooper.Shape)
    : List Instr :=
  (traverse shape .none (fun _ => .none)).fst ++ [.plain .unreachable]
where
  error (msg : String) : List Instr × Option IrTree.BlockExit :=
      ([.comment msg], .none)
  traverse (shape : ControlFlow.Relooper.Shape)
           (priorExit : Option IrTree.BlockExit)
           (loopBreak : Label → Option Label)
           : List Instr × Option IrTree.BlockExit :=
  match shape with
  | .simple l next =>
    match f.blocks.find? l with
    | .some block =>
      let body_instr := block.body.bind stmt
      let exit_instr := exit block.exit loopBreak
      let (next_instr, next_exit) :=
        match next with
        | .some n => traverse n (.some block.exit) loopBreak
        | .none   => ([], .none)

      ( body_instr ++ exit_instr ++ next_instr
      , match next_exit with | .none => .some block.exit | _ => next_exit
      )
    | .none =>
      error s!"WASM Trans: Could not find block labeled {l}, in shape {shape} in {f}!"

  | .loop inner next =>
    let break_lbls := ControlFlow.Relooper.Shape.getNext shape
    let lbls := ControlFlow.Relooper.Shape.getLabels shape
    match inner, lbls with
    | .some i, [i_lbl] =>
      let loopBreak' := fun l =>
        if l ∈ break_lbls then .some i_lbl else loopBreak l
      let (i_instr, body_exit) := traverse i .none loopBreak'
      let (n_instr, next_exit) :=
        match next with
        | .some n => traverse n body_exit loopBreak
        | .none   => ([], .none)

      let i_br :=
        match body_exit with
        | .some (.cjump t _ i_lbl? _) =>
          locl (.get (temp t))
          :: (if i_lbl = i_lbl? then [] else [i32_eqz])
          ++ [plain <|.br_if (label i_lbl)]
        | .some (.jump i_lbl?) =>
          if i_lbl = i_lbl? then [Plain.br (label i_lbl)] else []
        | _ =>
          error s!"WASM Trans Error: Shape loop, {shape}, body has improper exit {body_exit}!"
            |>.fst

      ( ( block i_lbl.toWasmLoopBreak [loop i_lbl.toWasmIdent (i_instr ++ i_br)]
        ) :: n_instr
      , next_exit
      )

    | .some _, _ =>
      error s!"WASM Trans: Shape loop, {shape}, has too many/few successors: {lbls}!"
    | .none, _ =>
      error s!"WASM Trans: Shape loop, {shape}, missing loop body!"

  | .multi left right next =>
    let lbls := ControlFlow.Relooper.Shape.getLabels shape
    match left, right, lbls, find_cjump f priorExit with
    | .some l, .some r, [l_lbl, r_lbl], .some (ct, tt, ff) =>
      let c_flip := if ff = l_lbl then [i32_eqz] else []
      let (l_instr, l_exit) := traverse l .none loopBreak
      let (r_instr, r_exit) := traverse r .none loopBreak
      let (n_instr, next_exit) :=
        match next with -- l_exit == r_exit
        | .some n => traverse n r_exit loopBreak
        | .none   => ([], .none)

      let cond :=
        [locl (.get (temp ct))]
        ++ c_flip
        ++ [.plain <|.br_if (label r_lbl)]
      let r_block := Instr.block <|
        .block r_lbl.toWasmIdent
          (.typeuse (.elab_param_res [] []))
          (cond ++ r_instr ++ [.plain <|.br (label l_lbl)])
          .wasm_end
          .none
      let l_block := Instr.block <|
        .block l_lbl.toWasmIdent
          (.typeuse (.elab_param_res [] []))
          (r_block :: l_instr)
          .wasm_end
          .none

      (l_block :: n_instr, next_exit)
    | _, _, _, _ =>
      error s!"WASM Trans: Shape multi, {shape}, doesn't have condition to branch: {priorExit}!"

  | .illegal _ => error s!"WASM Trans: Illegal shape {shape}!"

-- todo: temp just to get things working
partial def find_used_temps (instrs : List Instr) : List Ident :=
  instrs.foldl (fun acc i =>
    match i with
    | .block (.block _ _ body _ _)       => find_used_temps body ++ acc
    | .block (.loop _ _ body _ _)        => find_used_temps body ++ acc
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
  List.zip prog.funcs shapes |>.map (fun (f, s) => func f s)

/- Computes the data section of the WASM module, as described in `langs.md`. -/
def data (prog : IrTree.Prog) : Module.Data :=
  let free_seg := prog.str_size.toBytes
  let str_data := prog.str_map.bind (·.1.data.map (·.toUInt8 sorry) ++ [0])
  ⟨.none, ⟨free_seg ++ str_data, sorry⟩, .active 0 [i32_const 0]⟩
