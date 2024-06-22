/- C0deine - TST.Expr
   Expressions, these must be well typed by definition.
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Context

namespace C0deine.Tst

open Typ Numbers

inductive UnOp.Int  | neg | not deriving Inhabited, Lean.ToExpr
inductive UnOp.Bool | neg       deriving Inhabited, Lean.ToExpr
inductive UnOp
| int (op : UnOp.Int)
| bool (op : UnOp.Bool)
deriving Inhabited, Lean.ToExpr

inductive BinOp.Int
| plus | minus | times | div | mod | and | xor | or | lsh | rsh
deriving Inhabited, Lean.ToExpr

inductive BinOp.Bool
| and | or
deriving Inhabited, Lean.ToExpr

inductive BinOp
| int (op : BinOp.Int)
| cmp (op : Comparator)
| bool (op : BinOp.Bool)
deriving Inhabited, Lean.ToExpr

@[inline] def UnOp.type : UnOp → Typ
  | .int _  => .prim .int
  | .bool _ => .prim .bool

/- TST expressions are similar to the AST expressions but they are also encoded
   with type information such that an ill-typed TST-expression cannot be
   constructed. Another way of thinking about it is that these are both a
   representation of the language and the static rules themselves.

   One difference from the traditional static semantic rules is that we use
   "Fording" in some places. A traditional rule would specify that would have
   some type (e.g. `binop_int : int → int → int`). In our case this can cause
   problems when generating the TST and proving properties about it. So instead
   we allow sub-expressions to be any type, and then later require a proof that
   they are equal/equivalent to the required type (e.g.
   `binop_int : τ₁ → τ₁ = int → τ₂ → τ₂ = int → int`). We are allowing any type,
   so long as it's the correct one ("Any color [...], so long as it's black").
 -/
open Typ.Notation in
inductive Expr (Δ : GCtx) (Γ : FCtx) : (τ : Typ) → Type
| num  : (hτ : τ = (int))    → Int32  → Expr Δ Γ τ
| char : (hτ : τ = (char))   → Char   → Expr Δ Γ τ
| str  : (hτ : τ = (string)) → String → Expr Δ Γ τ
| var
  : {τ : Typ}
  → (x : Symbol)
  → Γ.syms x = .some (.var τ)
  → Expr Δ Γ τ
| «true»  : (hτ : τ = (bool))  → Expr Δ Γ τ
| «false» : (hτ : τ = (bool))  → Expr Δ Γ τ
| null    : (hτ : τ = (any *)) → Expr Δ Γ τ
| unop_int
  : (hτ₁ : τ₁.equiv (int))
  → (hτ₂ : τ = (int))
  → (op : UnOp.Int)
  → (e : Expr Δ Γ τ₁)
  → Expr Δ Γ τ
| unop_bool
  : (hτ₁ : τ₁.equiv (bool))
  → (hτ₂ : τ = (bool))
  → (op : UnOp.Bool)
  → (e : Expr Δ Γ τ₁)
  → Expr Δ Γ τ
| binop_int
  : (hτ₁ : τ₁ = (int))
  → (hτ₂ : τ₂ = (int))
  → (hτ  : τ  = (int))
  → (op : BinOp.Int)
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ τ
| binop_bool
  : (hτ₁ : τ₁ = (bool))
  → (hτ₂ : τ₂ = (bool))
  → (hτ  : τ  = (bool))
  → (op : BinOp.Bool)
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ τ
| binop_eq
  : (hτ : τ = (bool))
  → (op : Comparator)
  → op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → τ₁.equiv τ₂
  → τ₁.is_eqtype ∨ τ₂.is_eqtype
  → Expr Δ Γ τ
| binop_rel_int
  : (hτ₁ : τ₁ = (int))
  → (hτ₂ : τ₂ = (int))
  → (hτ  : τ  = (bool))
  → (op : Comparator)
  → ¬op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ τ
| binop_rel_char
  : (hτ₁ : τ₁ = (char))
  → (hτ₂ : τ₂ = (char))
  → (hτ  : τ = (bool))
  → (op : Comparator)
  → ¬op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ τ
| ternop
  : (hτ₁ : τ₁ = (bool))
  → (hτ : τ = τ₂.intersect τ₃)
  → (cond : Expr Δ Γ τ₁)
  → (tt : Expr Δ Γ τ₂)
  → (ff : Expr Δ Γ τ₃)
  → τ₂.equiv τ₃
  → Expr Δ Γ τ
| app
  : (f : Symbol)
  → Γ.syms f = .some (.func status)
  → (τs : Fin status.type.arity → Typ)
  → (eq : ∀ i, (status.type.argTys i).equiv (τs i))
  → (args : (i : Fin status.type.arity) → Expr Δ Γ (τs i))
  → Expr Δ Γ status.type.retTy
| alloc : (τ : Typ) → Expr Δ Γ (τ*)
| alloc_array
  : (hτ₁ : τ₁ = (int))
  → (τ : Typ)
  → Expr Δ Γ τ₁
  → Expr Δ Γ (τ[])
| dot
  : (hτ₁ : τ₁ = (struct s))
  → Expr Δ Γ τ₁
  → (field : Symbol)
  → Δ.struct s = .some ⟨struct_fields, true⟩
  → struct_fields field = .some τ
  → Expr Δ Γ τ
| deref
  : (hτ₁ : τ₁ = (τ*))
  → Expr Δ Γ τ₁
  → Expr Δ Γ τ
| index
  : (hτ₁ : τ₁ = (τ[]))
  → (hτ₂ : τ₂ = (int))
  → Expr Δ Γ τ₁
  → Expr Δ Γ τ₂
  → Expr Δ Γ τ
| result
  : Γ.ret = some τ
  → Expr Δ Γ τ
| length
  : (hτ₁ : τ₁ = (τ[]))
  → Expr Δ Γ τ₁
  → Expr Δ Γ (int)

namespace Expr
open Typ.Notation

/- Assert that P can be folded to some value through every sub-expression -/
inductive Fold {Δ : GCtx} {Γ : FCtx}
    : (P : (τ : Typ) → α → Expr Δ Γ τ → Option α)
    → α → Expr Δ Γ τ → α → Prop
| num
  : {a₁ a₂ : α}
  → {hτ : τ = (int)}
  → P τ a₁ ((.num hτ v)) = some a₂
  → Fold P a₁ ((.num hτ v)) a₂
| char
  : {a₁ a₂ : α}
  → {hτ : τ = (char)}
  → P τ a₁ (.char hτ c) = some a₂
  → Fold P a₁ ((.char hτ c)) a₂
| str
  : {a₁ a₂ : α}
  → {hτ : τ = (string)}
  → P _ a₁ (.str hτ s) = some a₂
  → Fold P a₁ ((.str hτ s)) a₂
| var
  : {a₁ a₂ : α}
  → {h : Γ.syms x = .some (.var τ)}
  → P τ a₁ (.var x h) = some a₂
  → Fold P a₁ ((.var x h) : Expr Δ Γ _) a₂
| «true»
  : {a₁ a₂ : α}
  → {hτ : τ = (bool)}
  → P τ a₁ (.true hτ) = some a₂
  → Fold P a₁ (.true hτ) a₂
| «false»
  : {a₁ a₂ : α}
  → {hτ : τ = (bool)}
  → P τ a₁ (.false hτ) = some a₂
  → Fold P a₁ (.false hτ) a₂
| null
  : {a₁ a₂ : α}
  → {hτ : τ = (any *)}
  → P _ a₁ (.null hτ) = some a₂
  → Fold P a₁ (.null hτ) a₂
| unop_int
  : {a₁ a₂ a₃ : α}
  → {e : Expr Δ Γ τ₁}
  → {hτ₁ : τ₁.equiv (int)}
  → {hτ₂ : τ = (int)}
  → Fold P a₁ e a₂
  → P _ a₂ (.unop_int hτ₁ hτ₂ op e) = some a₃
  → Fold P a₁ (.unop_int hτ₁ hτ₂ op e) a₃
| unop_bool
  : {a₁ a₂ a₃ : α}
  → {e : Expr Δ Γ τ₁}
  → {hτ₁ : τ₁.equiv (bool)}
  → {hτ₂ : τ = (bool)}
  → Fold P a₁ e a₂
  → P _ a₂ (.unop_bool hτ₁ hτ₂ op e) = some a₃
  → Fold P a₁ (.unop_bool hτ₁ hτ₂ op e) a₃
| binop_int
  : {a₁ a₂ a₃ a₄ : α}
  → {l : Expr Δ Γ τ₁}
  → {r : Expr Δ Γ τ₂}
  → {hτ₁ : τ₁ = (int)}
  → {hτ₂ : τ₂ = (int)}
  → {hτ  : τ = (int)}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_int hτ₁ hτ₂ hτ op l r) = some a₄
  → Fold P a₁ (.binop_int hτ₁ hτ₂ hτ op l r) a₄
| binop_bool
  : {a₁ a₂ a₃ a₄ : α}
  → {l : Expr Δ Γ τ₁}
  → {r : Expr Δ Γ τ₂}
  → {hτ₁ : τ₁ = (bool)}
  → {hτ₂ : τ₂ = (bool)}
  → {hτ  : τ = (bool)}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_bool hτ₁ hτ₂ hτ op l r) = some a₄
  → Fold P a₁ (.binop_bool hτ₁ hτ₂ hτ op l r) a₄
| binop_eq
  : {a₁ a₂ a₃ a₄ : α}
  → {hτ : τ = (bool)}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_eq hτ op eq l r h₁ h₂) = some a₄
  → Fold P a₁ (.binop_eq hτ op eq l r h₁ h₂) a₄
| binop_rel_int
  : {a₁ a₂ a₃ a₄ : α}
  → {l : Expr Δ Γ τ₁}
  → {r : Expr Δ Γ τ₂}
  → {hτ₁ : τ₁ = (int)}
  → {hτ₂ : τ₂ = (int)}
  → {hτ  : τ = (bool)}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_rel_int hτ₁ hτ₂ hτ op eq l r) = some a₄
  → Fold P a₁ (.binop_rel_int hτ₁ hτ₂ hτ op eq l r) a₄
| binop_rel_char
  : {a₁ a₂ a₃ a₄ : α}
  → {l : Expr Δ Γ τ₁}
  → {r : Expr Δ Γ τ₂}
  → {hτ₁ : τ₁ = (char)}
  → {hτ₂ : τ₂ = (char)}
  → {hτ  : τ = (bool)}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_rel_char hτ₁ hτ₂ hτ op eq l r) = some a₄
  → Fold P a₁ (.binop_rel_char hτ₁ hτ₂ hτ op eq l r) a₄
| ternop
  : {a₁ a₂ a₃ a₄ a₅ : α}
  → {cc : Expr Δ Γ τ₁}
  → {tt : Expr Δ Γ τ₂}
  → {ff : Expr Δ Γ τ₃}
  → {hτ₁ : τ₁ = (bool)}
  → {hτ : τ = τ₂.intersect τ₃}
  → Fold P a₁ cc a₂
  → Fold P a₂ tt a₃
  → Fold P a₃ ff a₄
  → P _ a₄ (.ternop hτ₁ hτ cc tt ff h₂) = some a₅
  → Fold P a₁ (.ternop hτ₁ hτ cc tt ff h₂) a₅
| app
  : {a₁ a₂ a₃ : α}
  → {hsig : Γ.syms f = .some (.func status)}
  → {τs : Fin (status.type.arity) → Typ}
  → {eq : ∀ i, (status.type.argTys i).equiv (τs i)}
  → {args : (i : Fin status.type.arity) → Expr Δ Γ (τs i)}
  → (∀ i : Fin status.type.arity, -- nb not sequential nor joins
      Fold P a₁ (args i) a₂ )
  → P _ a₂ (.app f hsig τs eq args) = some a₃
  → Fold P a₁ (.app f hsig τs eq args) a₃
| alloc
  : {a₁ a₂ : α}
  → P _ a₁ (.alloc τ₁) = some a₂
  → Fold P a₁ (.alloc τ₁) a₂
| alloc_array
  : {a₁ a₂ a₃ : α}
  → {e : Expr Δ Γ τ₁}
  → {hτ₁ : τ₁ = (int)}
  → Fold P a₁ e a₂
  → P _ a₂ (.alloc_array hτ₁ τ e) = some a₃
  → Fold P a₁ (.alloc_array hτ₁ τ e) a₃
| dot
  : {a₁ a₂ a₃ : α}
  → {e : Expr Δ Γ τ₁}
  → {hτ₁ : τ₁ = (struct s)}
  → Fold P a₁ e a₂
  → P _ a₂ (.dot hτ₁ e f h₁ h₂) = some a₃
  → Fold P a₁ (.dot hτ₁ e f h₁ h₂) a₃
| deref
  : {a₁ a₂ a₃ : α}
  → {e : Expr Δ Γ τ₁}
  → {hτ₁ : τ₁ = (τ*)}
  → Fold P a₁ e a₂
  → P _ a₂ (.deref hτ₁ e) = some a₃
  → Fold P a₁ (.deref hτ₁ e) a₃
| index
  : {a₁ a₂ a₃ : α}
  → {e : Expr Δ Γ τ₁}
  → {indx : Expr Δ Γ τ₂}
  → {hτ₁ : τ₁ = (τ[])}
  → {hτ₂ : τ₂ = (int)}
  → Fold P a₁ e a₂
  → Fold P a₂ indx a₃
  → P _ a₃ (.index hτ₁ hτ₂ e indx) = some a₄
  → Fold P a₁ (.index hτ₁ hτ₂ e indx) a₄
| result
  : {a₁ a₂ : α}
  → P (τ := τ) a₁ (.result h) = some a₂
  → Fold P a₁ (.result h : Expr Δ Γ τ) a₂
| length
  : {a₁ a₂ a₃ : α}
  → {e : Expr Δ Γ τ₁}
  → {hτ₁ : τ₁ = (τ[])}
  → Fold P a₁ e a₂
  → P _ a₂ (.length hτ₁ e) = some a₃
  → Fold P a₁ (.length hτ₁ e) a₃

def All (P : {τ : Typ} → Expr Δ Γ τ → Bool) (e : Expr Δ Γ τ) : Prop :=
  Expr.Fold (fun _ _ e => if P e then some () else none) () e ()

@[inline] def only_contract : Expr Δ Γ τ → Bool
  | .result _   => .true
  | .length _ _ => .true
  | _           => .false
@[inline] def has_result : Expr Δ Γ τ → Bool
  | .result _  => .true
  | _          => .false

@[inline] def no_contract : Expr Δ Γ τ → Bool :=
  .not ∘ only_contract
@[inline] def no_result   : Expr Δ Γ τ → Bool :=
  .not ∘ has_result

abbrev NoContract Δ Γ τ := {e : Expr Δ Γ τ // All no_contract e}
abbrev NoResult   Δ Γ τ := {e : Expr Δ Γ τ // All no_result   e}

end Expr


def UnOp.Int.toString : UnOp.Int → String
  | neg => "~"
  | not => "!"
instance : ToString UnOp.Int where toString := UnOp.Int.toString

def UnOp.Bool.toString : UnOp.Bool → String
  | neg => "!"
instance : ToString UnOp.Bool where toString := UnOp.Bool.toString

def UnOp.toString : UnOp → String
  | int op  => s!"{op}"
  | bool op => s!"{op}"
instance : ToString UnOp where toString := UnOp.toString


def BinOp.Int.toString : BinOp.Int → String
  | .plus  => "+"
  | .minus => "-"
  | .times => "*"
  | .div   => "/"
  | .mod   => "%"
  | .and   => "&"
  | .xor   => "^"
  | .or    => "|"
  | .lsh   => "<<"
  | .rsh   => ">>"
instance : ToString BinOp.Int where toString := BinOp.Int.toString

def BinOp.Bool.toString : BinOp.Bool → String
  | .and => "&&"
  | .or  => "||"
instance : ToString BinOp.Bool where toString := BinOp.Bool.toString

def BinOp.toString : BinOp → String
  | .int op  => s!"{op}"
  | .cmp op  => s!"{op}"
  | .bool op => s!"{op}"
instance : ToString BinOp where toString := BinOp.toString

def Expr.toString : Expr Δ Γ τ → String
  | .num _ v            => s!"({v} : {τ})"
  | .char _ c           => s!"('{c.toString.sanitise}' : {τ})"
  | .str _ s            => s!"(\"{s.sanitise}\" : {τ})"
  | .«true» _           => s!"(true : {τ})"
  | .«false» _          => s!"(false : {τ})"
  | .null _             => s!"(NULL : {τ})"
  | .unop_int _ _ op e  => s!"({op}{Expr.toString e} : {τ})"
  | .unop_bool _ _ op e => s!"({op}{Expr.toString e} : {τ})"
  | .binop_int _ _ _ op l r
  | .binop_bool _ _ _ op l r
  | .binop_eq _ op _ l r _ _
  | .binop_rel_int _ _ _ op _ l r
  | .binop_rel_char _ _ _ op _ l r =>
    s!"({Expr.toString l} {op} {Expr.toString r} : {τ})"
  | .ternop _ _ cc tt ff _ =>
    s!"({Expr.toString cc} ? {Expr.toString tt} : {Expr.toString ff} : {τ})"
  | .app f _ _ _ args =>
    let str_args := ", ".intercalate
      (.ofFn (fun i => Expr.toString (args i)))
    s!"({f}({str_args}) : {τ})"
  | .alloc ty           => s!"(alloc({ty}) : {τ})"
  | .alloc_array _ ty e => s!"(alloc_array({ty}, {Expr.toString e}) : {τ})"
  | .var name _         => s!"({name} : {τ})"
  | .dot _ e field _ _  => s!"({Expr.toString e}.{field} : {τ})"
  | .deref _ e          => s!"(*{Expr.toString e} : {τ})"
  | .index _ _ e i      => s!"({Expr.toString e}[{Expr.toString i}] : {τ})"
  | .result _           => s!"(\\result : {τ})"
  | .length _ e         => s!"(\\length {Expr.toString e} : {τ})"

instance : ToString (Expr Δ Γ τ) := ⟨Expr.toString⟩
