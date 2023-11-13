import C0deine.AuxDefs
import C0deine.Parser.Ast

namespace C0deine.Dynamics

open Ast

inductive Exception
| memory
| arithmetic
| abort

inductive Address
| var : Ident → Address
| ref : Nat → Address

inductive Value
| num : Int32 → Value
| «true» | «false»
| nothing
| ptr : Option Nat → Value
deriving Inhabited, Repr

inductive BinOp
| int (op : BinOp.Int)
| cmp (op : Comparator)

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
| app       : Ident → Cont .val → Cont .val                  -- f(_)
| arg       : List Value → List Expr → Cont .val → Cont .val -- (vs,_,es)
| alloc_arr : Typ → Cont .val → Cont .val                    -- alloc_array(t,_)
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

notation:50 lhs:51 " ▷ " rhs:51 => DynResult.eval lhs rhs
notation:50 lhs:51 " ▸ " rhs:51 => DynResult.exec lhs rhs

def Environment := Symbol.Map Value
def Environment.empty : Environment := Symbol.Map.empty

structure StackFrame where
  environment : Environment
  continuation : Cont r

structure Heap where
  data : Std.HashMap Nat Value
  next : Nat

def Heap.empty : Heap :=
  { data := Std.HashMap.empty
  , next := 0
  }

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


inductive Step : (H : Heap) → (S : List StackFrame) → (η : Environment) → DynResult → Prop
| num
  : Step H S η (.eval (.num c) K)
  → Step H S η (.val (.num c) K)
| «true»
  : Step H S η (.eval .true K)
  → Step H S η (.val .true K)
| «false»
  : Step H S η (.eval .false K)
  → Step H S η (.val .false K)
| null
  : Step H S η (.eval .null K)
  → Step H S η (.val (.ptr .none) K)
| unop
  : Step H S η (.eval (.unop op e) K)
  → Step H S η (.eval e (.unop op K))
| unop_res
  : Step H S η (.val c (.unop op K))
  → Step.UnOp op c v
  → Step H S η (.val v K)
| binop_int₁
  : Step H S η (.eval (.binop (.int op) e₁ e₂) K)
  → Step H S η (.eval e₁ (.binop₁ (.int op) e₂ K))
| binop_int₂
  : Step H S η (.val c₁ (.binop₁ (.int op) e₂ K))
  → Step H S η (.eval e₂ (.binop₂ c₁ (.int op) K))
| binop_cmp₁
  : Step H S η (.eval (.binop (.cmp op) e₁ e₂) K)
  → Step H S η (.eval e₁ (.binop₁ (.cmp op) e₂ K))
| binop_cmp₂
  : Step H S η (.val c₁ (.binop₁ (.cmp op) e₂ K))
  → Step H S η (.eval e₂ (.binop₂ c₁ (.cmp op) K))
| binop_res
  : Step H S η (.val c₂ (.binop₂ c₁ op K))
  → Step.BinOp c₁ op c₂ (.inl v)
  → Step H S η (.val v K)
| binop_exn
  : Step H S η (.val c₂ (.binop₂ c₁ op K))
  → Step.BinOp c₁ op c₂ (.inr exn)
  → Step H S η (.exn exn)
| and₁
  : Step H S η (.eval (.binop (.bool .and) e₁ e₂) K)
  → Step H S η (.eval e₁ (.and e₂ K))
| and₂
  : Step H S η (.val .true (.and e₂ K))
  → Step H S η (.eval e₂ K)
| and_sc
  : Step H S η (.val .false (.and e₂ K))
  → Step H S η (.val .false K)
| or₁
  : Step H S η (.eval (.binop (.bool .or) e₁ e₂) K)
  → Step H S η (.eval e₁ (.or e₂ K))
| or₂
  : Step H S η (.val .false (.or e₂ K))
  → Step H S η (.eval e₂ K)
| or_sc
  : Step H S η (.val .true (.or e₂ K))
  → Step H S η (.val .true K)
| ternop
  : Step H S η (.eval (.ternop cc tt ff) K)
  → Step H S η (.eval cc (.ternop tt ff K))
| ternop_t
  : Step H S η (.val .true (.ternop tt ff K))
  → Step H S η (.eval tt K)
| ternop_f
  : Step H S η (.val .false (.ternop tt ff K))
  → Step H S η (.eval ff K)
-- | app
  -- : Step H S η (.eval (.app f []) K)
  -- → Step H (⟨η, K⟩ :: S) (Environment.empty) (.exec sorry .nil)
-- todo app
-- todo alloc
-- todo alloc_array
| var
  : Step H S η (.eval (.var x) K)
  → Step H S η (.val (η.find! x) K)
-- todo dot
-- todo arrow
-- todo deref
-- todo index
/- STATEMENTS -/
| decl_none
  : Step H S η (.exec (.decl τ x .none body) K)
  → Step H S (η.insert x .nothing) (.exec_seq body K)
| decl_assn
  : Step H S η (.exec (.decl τ x (.some e) body) K)
  → Step H S (η.insert x .nothing) (.eval e (K.consStmtList body))
| assn_var_eq₁
  : Step H S η (.exec (.assn (.var x) .eq e) K)
  → Step H S η (.eval e (.assn_var x K))
| assn_var_eq₂
  : Step H S η (.val v (.assn_var x K))
  → Step H S (η.insert x v) (.nop K)
| assn_var_op
  : Step H S η (.exec (.assn (.var x) (.aseq op) e) K)
  → Step H S η (.exec (.assn (.var x) .eq (.binop (.int op) (.var x) e)) K)
| assn_addr₁
  : Step H S η (.exec (.assn lv op e) K)
  → Step H S η (.eval lv.toExpr (.assn₁ e op K))
| assn_addr₂
  : Step H S η (.val v (.assn₁ e op K))
-- todo assn
| ite
  : Step H S η (.exec (.ite e tt ff) K)
  → Step H S η (.eval e (.ite tt ff K))
| ite_t
  : Step H S η (.val .true (.ite tt ff K))
  → Step H S η (.exec_seq tt K)
| ite_f
  : Step H S η (.val .false (.ite tt ff K))
  → Step H S η (.exec_seq ff K)
| while
  : Step H S η (.exec (.while e body) K)
  → Step H S η (.exec (.ite e (body.append [.while e body]) []) K)
| return_val₁
  : Step H S η (.exec (.return (.some e)) K)
  → Step H S η (.eval e .return)
| return_main
  : Step H [] η (.val (.num c) .return)
  → Step H [] η (.res c)
| return_val₂
  : Step H (frame :: S) η (.val v .return)
  → Step H S frame.environment (.val v frame.continuation)
| return_none
  : Step H (frame :: S) η (.exec (.return .none) K)
  → Step H S frame.environment (.nop frame.continuation)
| assert
  : Step H S η (.exec (.assert e) K)
  → Step H S η (.eval e (.assert K))
| assert_t
  : Step H S η (.val .true (.assert K))
  → Step H S η (.nop K)
| assert_f
  : Step H S η (.val .false (.assert K))
  → Step H S η (.exn .abort)
| exp₁
  : Step H S η (.exec (.exp e) K)
  → Step H S η (.eval e (.discard K))
| exp₂
  : Step H S η (.val v (.discard K))
  → Step H S η (.nop K)
