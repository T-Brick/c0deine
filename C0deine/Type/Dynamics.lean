import C0deine.AuxDefs
import C0deine.Ast.Ast
import C0deine.Type.Statics

namespace C0deine.Ast.Dynamics

open Ast
open Statics

inductive Exception
| memory
| arithmetic
| abort

inductive Address
| ref : Nat → Address
| null : Address
deriving Inhabited, Repr

inductive Value
| num : Int32 → Value
| «true» | «false»
| nothing
| addr : Address → Value
| struct : (Ident → Value) → Value
| arr : List Value → Value
deriving Inhabited

inductive BinOp
| int (op : BinOp.Int)
| cmp (op : Comparator)

inductive TypeValue : Value → Statics.Typ → Prop
| num     : TypeValue (.num i) .int
| «true»  : TypeValue .true .bool
| «false» : TypeValue .false .bool
| ptr     : TypeValue (.addr a) (.ptr ty) -- todo is this right?
| arr     : TypeValue (.addr a) (.arr τ)  --      should check heap?
-- todo finish

inductive Default : Statics.Typ → Value → Prop
| int    : Default .int (.num 0)
| bool   : Default .bool .false
| ptr    : Default (.ptr t) (.addr .null)
| struct : Default (.struct t) (.addr .null)
| arr    : Default (.arr t) (.addr .null)

inductive IsExtern
  : (Δ : ProgTc (p : Prog))
  → (type : Option Typ)
  → (f : Ident)
  → (params : List Param)
  → Prop
where
| extern : (GDecl.fdecl ⟨type, f, params⟩) ∈ Prog.program p
         → IsExtern Δ type f params

inductive FindFDef
  : (Δ : ProgTc (p : Prog))
  → (type : Option Typ)
  → (f : Ident)
  → (params : List Param)
  → (body : List Stmt)
  → Prop
where
| body : (GDecl.fdef ⟨⟨type, f, params⟩, body⟩) ∈ Prog.program p
       → FindFDef Δ type f params body

-- continuation frames can result in a value or an address
--  importantly, addresses are just the intermediate results, they aren't
--  the same as addresses computed by `alloc`, etc.
inductive Cont.Res | val | addr

-- merge Cont and ContFrame from the lecture notes bc of addressing modalities
inductive Cont : Cont.Res → Type
| nil       : Cont .val                                      -- ·
| unop      : UnOp → Cont .val → Cont .val                   -- op _
| binop₁    : BinOp → Expr → Cont .val → Cont .val           -- _ ⊕ e
| binop₂    : Value → BinOp → Cont .val → Cont .val          -- c ⊕ _
| and       : Expr → Cont .val → Cont .val                   -- _ && e
| or        : Expr → Cont .val → Cont .val                   -- _ || e
| ternop    : Expr → Expr → Cont .val → Cont .val            -- _ ? e₁ : e₂
| app       : Ident → List Value → List Expr
                    → Cont .val → Cont .val                  -- f(vs,_,es)
| alloc_arr : Statics.Typ → Cont .val → Cont .val            -- alloc_array(τ,_)
| dot       : Ident → Cont .addr → Cont .addr                -- &(_.f)
| deref     : Cont .val → Cont .addr                         -- *_
| index₁    : Expr → Cont .addr → Cont .val                  -- &(_[e])
| index₂    : Address → Cont .addr → Cont .val               -- &(a[_])
| stmt      : Stmt → Cont .val → Cont .val                   -- s
| assn₁     : Expr → AsnOp → Cont .val → Cont .addr          -- assn(_, op, e)
| assn₂     : Address → AsnOp → Cont .val → Cont .val        -- assn(a, op, _)
| assn_var  : Ident → Cont .val → Cont .val                  -- assn(x, _)
| ite       : List Stmt → List Stmt → Cont .val → Cont .val  -- if(_, s₁, s₂)
| «while»   : List Stmt → Cont .val → Cont .val              -- while(_){...}
| «return»  : Cont .val                                      -- return _
| assert    : Cont .val → Cont .val                          -- assert(_)
| discard   : Cont .val → Cont .val                          -- discard

def Cont.consStmtList (K : Cont .val) : List Stmt → Cont .val
  | [] => K
  | s :: stmts => .stmt s (consStmtList K stmts)

inductive DynResult : Prop
| val      : Value → Cont r → DynResult
| eval     : Expr → Cont r → DynResult
| exec     : Stmt → Cont r → DynResult
| exec_seq : List Stmt → Cont r → DynResult
| exn      : Exception → DynResult
| nop      : Cont r → DynResult -- maybe move into AST
| res      : Int32 → DynResult


def Environment := Symbol → Option Value

namespace Environment

def empty : Environment := fun _ => .none
def update (η : Environment) (x : Symbol) (v : Value) : Environment :=
  Function.update η x v

def find! (η : Environment) (x : Symbol) : Value :=
  match η x with
  | .none   => panic! s!"var not found"
  | .some v => v

def ofLists (params : List Param) (vargs : List Value) : Environment :=
  List.zip params vargs
  |>.foldl (fun η (p, v) => η.update p.name v) Environment.empty

end Environment

structure StackFrame where
  environment : Environment
  continuation : Cont .val

structure Heap where
  data : Nat → Option Value
  next : Nat

namespace Heap

def empty : Heap := { data := fun _ => .none, next := 0 }
def update (H : Heap) (a : Nat) (v : Value) : Heap :=
  { data := Function.update H.data a v, next := H.next }

def find (H : Heap) : Address → Value ⊕ Exception
  | .null => .inr .memory
  | .ref a =>
    match H.data a with
    | .none => .inr .memory
    | .some v => .inl v

def add (H : Heap) (v : Value) : Address × Heap :=
  (.ref H.next, ⟨fun a => if a = H.next then v else H.data a, H.next + 1⟩)

end Heap

inductive Step.UnOp : UnOp → Value → Value → Prop
| int_neg : UnOp (.int .neg)  (.num c) (.num (-c))
| int_not : UnOp (.int .not)  (.num c) (.num c.not)
| neg_t   : UnOp (.bool .neg) (.true)  (.false)
| neg_f   : UnOp (.bool .neg) (.false) (.true)

def Step.ofNum : Int32 → Value ⊕ Exception := .inl ∘ .num

def Step.ofNum_exn : Option Int32 → Value ⊕ Exception
  | .none => .inr .arithmetic
  | .some i => .inl (.num i)

def Step.bool : Bool → Value ⊕ Exception
  | true  => .inl .true
  | false => .inl .false

inductive Step.BinOp : Value → BinOp → Value → Value ⊕ Exception → Prop
| add : BinOp (.num c₁) (.int .plus)          (.num c₂) (ofNum (c₁ + c₂))
| sub : BinOp (.num c₁) (.int .minus)         (.num c₂) (ofNum (c₁ - c₂))
| mul : BinOp (.num c₁) (.int .times)         (.num c₂) (ofNum (c₁ * c₂))
| div : BinOp (.num c₁) (.int .div)           (.num c₂) (ofNum_exn (c₁ / c₂))
| mod : BinOp (.num c₁) (.int .mod)           (.num c₂) (ofNum_exn (c₁ % c₂))
| and : BinOp (.num c₁) (.int .and)           (.num c₂) (ofNum (c₁ &&& c₂))
| xor : BinOp (.num c₁) (.int .xor)           (.num c₂) (ofNum (c₁ ^^^ c₂))
| or  : BinOp (.num c₁) (.int .or)            (.num c₂) (ofNum (c₁ ||| c₂))
| lsh : BinOp (.num c₁) (.int .lsh)           (.num c₂) (ofNum (c₁ <<< c₂))
| rsh : BinOp (.num c₁) (.int .rsh)           (.num c₂) (ofNum (c₁ >>> c₂))
| lt  : BinOp (.num c₁) (.cmp .less)          (.num c₂) (bool (c₁ < c₂))
| gt  : BinOp (.num c₁) (.cmp .greater)       (.num c₂) (bool (c₁ > c₂))
| eq  : BinOp (.num c₁) (.cmp .equal)         (.num c₂) (bool (c₁ = c₂))
| ne  : BinOp (.num c₁) (.cmp .not_equal)     (.num c₂) (bool (c₁ ≠ c₂))
| le  : BinOp (.num c₁) (.cmp .less_equal)    (.num c₂) (bool (c₁ ≤ c₂))
| ge  : BinOp (.num c₁) (.cmp .greater_equal) (.num c₂) (bool (c₁ ≥ c₂))

structure State (p : Prog) where
  Δ : ProgTc p
  H : Heap
  S : List StackFrame
  η : Environment
  r : DynResult

local notation:50 Δ:51 " ; " H:51 " ; " S:51 " ; " η:51 " |= " r:51 =>
  State.mk Δ H S η r

inductive Step : State p → State p → Prop
| num
  : Step (Δ; H; S; η |= (.eval (.num c) K))
         (Δ; H; S; η |= (.val  (.num c) K))
| «true»
  : Step (Δ; H; S; η |= (.eval .true K))
         (Δ; H; S; η |= (.val  .true K))
| «false»
  : Step (Δ; H; S; η |= (.eval .false K))
         (Δ; H; S; η |= (.val  .false K))
| null
  : Step (Δ; H; S; η |= (.eval .null         K))
         (Δ; H; S; η |= (.val  (.addr .null) K))
| unop
  : Step (Δ; H; S; η |= (.eval (.unop op e) K))
         (Δ; H; S; η |= (.eval e (.unop op K)))
| unop_res
  : Step.UnOp op c v
  → Step (Δ; H; S; η |= (.val c (.unop op K)))
         (Δ; H; S; η |= (.val v K))
| binop_int₁
  : Step (Δ; H; S; η |= (.eval (.binop (.int op) e₁ e₂) K))
         (Δ; H; S; η |= (.eval e₁ (.binop₁ (.int op) e₂ K)))
| binop_int₂
  : Step (Δ; H; S; η |= (.val c₁ (.binop₁ (.int op) e₂ K)))
         (Δ; H; S; η |= (.eval e₂ (.binop₂ c₁ (.int op) K)))
| binop_cmp₁
  : Step (Δ; H; S; η |= (.eval (.binop (.cmp op) e₁ e₂) K))
         (Δ; H; S; η |= (.eval e₁ (.binop₁ (.cmp op) e₂ K)))
| binop_cmp₂
  : Step (Δ; H; S; η |= (.val c₁ (.binop₁ (.cmp op) e₂ K)))
         (Δ; H; S; η |= (.eval e₂ (.binop₂ c₁ (.cmp op) K)))
| binop_res
  : Step.BinOp c₁ op c₂ (.inl v)
  → Step (Δ; H; S; η |= (.val c₂ (.binop₂ c₁ op K)))
         (Δ; H; S; η |= (.val v K))
| binop_exn
  : Step.BinOp c₁ op c₂ (.inr exn)
  → Step (Δ; H; S; η |=  (.val c₂ (.binop₂ c₁ op K)))
         (Δ; H; S; η |=  (.exn exn))
| and₁
  : Step (Δ; H; S; η |= (.eval (.binop (.bool .and) e₁ e₂) K))
         (Δ; H; S; η |= (.eval e₁ (.and e₂ K)))
| and₂
  : Step (Δ; H; S; η |= (.val .true (.and e₂ K)))
         (Δ; H; S; η |= (.eval e₂ K))
| and_sc
  : Step (Δ; H; S; η |= (.val .false (.and e₂ K)))
         (Δ; H; S; η |= (.val .false K))
| or₁
  : Step (Δ; H; S; η |= (.eval (.binop (.bool .or) e₁ e₂) K))
         (Δ; H; S; η |= (.eval e₁ (.or e₂ K)))
| or₂
  : Step (Δ; H; S; η |= (.val .false (.or e₂ K)))
         (Δ; H; S; η |= (.eval e₂ K))
| or_sc
  : Step (Δ; H; S; η |= (.val .true (.or e₂ K)))
         (Δ; H; S; η |= (.val .true K))
| ternop
  : Step (Δ; H; S; η |= (.eval (.ternop cc tt ff) K))
         (Δ; H; S; η |= (.eval cc (.ternop tt ff K)))
| ternop_t
  : Step (Δ; H; S; η |= (.val .true (.ternop tt ff K)))
         (Δ; H; S; η |= (.eval tt K))
| ternop_f
  : Step (Δ; H; S; η |= (.val .false (.ternop tt ff K)))
         (Δ; H; S; η |= (.eval ff K))
-- todo generalise this a bit : )
| app_args
  : Step (Δ; H; S; η |= (.eval (.app f (e::args)) K))
         (Δ; H; S; η |= (.eval e (.app f [] args K)))
| app_args_cont
  : Step (Δ; H; S; η |= (.val v (.app f vargs (e::args) K)))
         (Δ; H; S; η |= (.eval e (.app f (vargs ++ [v]) args K)))
| app_args_call
  : FindFDef Δ τ_opt f ps body
  → Step (Δ; H; S; η |= (.val v (.app f vargs [] K)))
         (Δ; H; (⟨η, K⟩::S); (Environment.ofLists ps vargs) |= (.exec_seq body .nil))
| app_args_extern_nonvoid
  : IsExtern Δ (.some ty) f params
  → TypResolves Δ.prog_ctx ty τ
  → (H' : Heap)
  → TypeValue res τ
  → Step (Δ; H ; S; η |= (.val v (.app f vargs [] K)))
         (Δ; H'; S; η |= (.val res K))
| app_args_extern_void
  : IsExtern Δ .none f params
  → (H' : Heap)
  → Step (Δ; H ; S; η |= (.val v (.app f vargs [] K)))
         (Δ; H'; S; η |= (.nop K))
| app_unit_extern_nonvoid
  : IsExtern Δ (.some ty) f params
  → TypResolves Δ.prog_ctx ty τ
  → (H' : Heap)
  → TypeValue res τ
  → Step (Δ; H ; S; η |= (.eval (.app f []) K))
         (Δ; H'; S; η |= (.val res K))
| app_unit_extern_void
  : IsExtern Δ .none f params
  → (H' : Heap)
  → Step (Δ; H ; S; η |= (.eval (.app f []) K))
         (Δ; H'; S; η |= (.nop K))
| app_unit_call
  : FindFDef Δ τ_opt f params body
  → Step (Δ; H; S; η |= (.eval (.app f []) K))
         (Δ; H; (⟨η, K⟩ :: S); (Environment.empty) |= (.exec_seq body .nil))
-- todo app
| alloc
  : TypResolves Δ.prog_ctx ty τ
  → Default τ v
  → H.add v = (a, H')
  → Step (Δ; H ; S; η |= (.eval (.alloc ty) K))
         (Δ; H'; S; η |= (.val (.addr a) K))
| alloc_array
  : TypResolves Δ.prog_ctx ty τ
  → Step (Δ; H; S; η |= (.eval (.alloc_array ty e) K))
         (Δ; H; S; η |= (.eval e (.alloc_arr τ K)))
| alloc_array_lt_zero
  : n < 0
  → Step (Δ; H; S; η |= (.val (.num n) (.alloc_arr τ K)))
         (Δ; H; S; η |= (.exn .memory))
| alloc_array_val
  : n ≥ 0
  → Default τ v
  → H.add (.arr (List.ofFn (n := n.toNat) (fun _ => v))) = (a, H')
  → Step (Δ; H ; S; η |= (.val (.num n) (.alloc_arr τ K)))
         (Δ; H'; S; η |= (.val (.addr a) K))
| var
  : Step (Δ; H; S; η |= (.eval (.var x) K))
         (Δ; H; S; η |= (.val (η.find! x) K))
| dot
  : Step (Δ; H; S; η |= (.eval (.dot e f) K))
         (Δ; H; S; η |= (.eval e (.dot f K)))
| dot_val
  : Step (Δ; H; S; η |= (.val (.struct fields) (.dot f K)))
         (Δ; H; S; η |= (.val (fields f) K))
| dot_null
  : Step (Δ; H; S; η |= (.val (.addr .null) (.dot f K)))
         (Δ; H; S; η |= (.exn .memory))
| arrow
  : Step (Δ; H; S; η |= (.eval (.arrow e f) K))
         (Δ; H; S; η |= (.eval (.dot (.deref e) f) K))
| deref₁
  : Step (Δ; H; S; η |= (.eval (.deref e) K))
         (Δ; H; S; η |= (.eval e (.deref K)))
| deref_val
  : H.find a = .inl v
  → Step (Δ; H; S; η |= (.val (.addr a) (.deref K)))
         (Δ; H; S; η |= (.val v K))
| deref_exn
  : H.find a = .inr exn
  → Step (Δ; H; S; η |= (.val (.addr a) (.deref K)))
         (Δ; H; S; η |= (.exn exn))
| index₁
  : Step (Δ; H; S; η |= (.eval (.index e₁ e₂) K))
         (Δ; H; S; η |= (.eval e₁ (.index₁ e₂ K)))
| index₂
  : Step (Δ; H; S; η |= (.val (.addr a) (.index₁ e₂ K)))
         (Δ; H; S; η |= (.eval e₂ (.index₂ a K)))
| index_val
  : H.find a = .inl (.arr arr)
  → (bounds : 0 ≤ i ∧ i.toNat < arr.length)
  → Step (Δ; H; S; η |= (.val (.num i) (.index₂ a K)))
         (Δ; H; S; η |= (.val (arr.get ⟨i.toNat, bounds.right⟩) K))
| index_lt_zero
  : H.find a = .inl (.arr arr)
  → i < 0
  → Step (Δ; H; S; η |= (.val (.num i) (.index₂ a K)))
         (Δ; H; S; η |= (.exn .memory))
| index_gt_length
  : H.find a = .inl (.arr arr)
  → i.toNat ≥ arr.length
  → Step (Δ; H; S; η |= (.val (.num i) (.index₂ a K)))
         (Δ; H; S; η |= (.exn .memory))
| index_null
  : H.find a = .inr exn
  → Step (Δ; H; S; η |= (.val i (.index₂ a K)))
         (Δ; H; S; η |= (.exn exn))
/- STATEMENTS -/
| decl_none
  : Step (Δ; H; S; η |= (.exec (.decl τ x .none body) K))
         (Δ; H; S; (η.update x .nothing) |= (.exec_seq body K))
| decl_assn
  : Step (Δ; H; S; η |= (.exec (.decl τ x (.some e) body) K))
         (Δ; H; S; (η.update x .nothing) |= (.eval e (K.consStmtList body)))
| assn_var_eq₁
  : Step (Δ; H; S; η |= (.exec (.assn (.var x) .eq e) K))
         (Δ; H; S; η |= (.eval e (.assn_var x K)))
| assn_var_eq₂
  : Step (Δ; H; S; η |= (.val v (.assn_var x K)))
         (Δ; H; S; (η.update x v) |= (.nop K))
| assn_var_op
  : Step (Δ; H; S; η |= (.exec (.assn (.var x) (.aseq op) e) K))
         (Δ; H; S; η |= (.exec (.assn (.var x) .eq (.binop (.int op) (.var x) e)) K))
| assn_addr₁
  : Step (Δ; H; S; η |= (.exec (.assn lv op e) K))
         (Δ; H; S; η |= (.eval lv.toExpr (.assn₁ e op K)))
| assn_addr₂
  : Step (Δ; H; S; η |= (.val (.addr a) (.assn₁ e op K)))
         (Δ; H; S; η |= (.eval e (.assn₂ a op K)))
| assn_addr_eq_val
  : Step (Δ; H; S; η |= (.val v (.assn₂ (.ref a) .eq K)))
         (Δ; (H.update a v); S; η |= (.nop K))
| assn_addr_null
  : Step (Δ; H; S; η |= (.val v (.assn₂ .null op K)))
         (Δ; H; S; η |= (.exn .memory))
| assn_addr_op_val                    -- todo: double check this probs
  : H.find a = .inl (.num da)
  → Step (Δ; H; S; η |= (.val (.num c) (.assn₂ a (.aseq op) K)))
         (Δ; H; S; η |= (.eval (.binop (.int op) (.num da) (.num c)) K))
| assn_addr_op_exn                    -- todo: likewise
  : H.find a = .inr exn
  → Step (Δ; H; S; η |= (.val (.num c) (.assn₂ a (.aseq op) K)))
         (Δ; H; S; η |= (.exn exn))
| ite
  : Step (Δ; H; S; η |= (.exec (.ite e tt ff) K))
         (Δ; H; S; η |= (.eval e (.ite tt ff K)))
| ite_t
  : Step (Δ; H; S; η |= (.val .true (.ite tt ff K)))
         (Δ; H; S; η |= (.exec_seq tt K))
| ite_f
  : Step (Δ; H; S; η |= (.val .false (.ite tt ff K)))
         (Δ; H; S; η |= (.exec_seq ff K))
| while
  : Step (Δ; H; S; η |= (.exec (.while e body) K))
         (Δ; H; S; η |= (.exec (.ite e (body.append [.while e body]) []) K))
| return_val₁
  : Step (Δ; H; S; η |= (.exec (.return (.some e)) K))
         (Δ; H; S; η |= (.eval e .return))
| return_main
  : Step (Δ; H; []; η |= (.val (.num c) .return))
         (Δ; H; []; η |= (.res c))
| return_val₂
  : Step (Δ; H; (frame :: S); η |= (.val v .return))
         (Δ; H; S; frame.environment |= (.val v frame.continuation))
| return_none
  : Step (Δ; H; (frame :: S); η |= (.exec (.return .none) K))
         (Δ; H; S; frame.environment |= (.nop frame.continuation))
| assert
  : Step (Δ; H; S; η |= (.exec (.assert e) K))
         (Δ; H; S; η |= (.eval e (.assert K)))
| assert_t
  : Step (Δ; H; S; η |= (.val .true (.assert K)))
         (Δ; H; S; η |= (.nop K))
| assert_f
  : Step (Δ; H; S; η |= (.val .false (.assert K)))
         (Δ; H; S; η |= (.exn .abort))
| exp₁
  : Step (Δ; H; S; η |= (.exec (.exp e) K))
         (Δ; H; S; η |= (.eval e (.discard K)))
| exp₂
  : Step (Δ; H; S; η |= (.val v (.discard K)))
         (Δ; H; S; η |= (.nop K))
