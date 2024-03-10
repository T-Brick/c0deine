/- C0deine - TST.Expr
   Expressions, these must be well typed by definition.
   - Thea Brick
 -/
import C0deine.Type.SyntaxTree.Context

namespace C0deine.Tst

open Typ

inductive UnOp.Int  | neg | not deriving Inhabited
inductive UnOp.Bool | neg       deriving Inhabited
inductive UnOp
| int (op : UnOp.Int)
| bool (op : UnOp.Bool)
deriving Inhabited

inductive BinOp.Int
| plus | minus | times | div | mod | and | xor | or | lsh | rsh
deriving Inhabited

inductive BinOp.Bool
| and | or
deriving Inhabited

inductive BinOp
| int (op : BinOp.Int)
| cmp (op : Comparator)
| bool (op : BinOp.Bool)
deriving Inhabited

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
| num  : Int32  → Expr Δ Γ (int)
| char : Char   → Expr Δ Γ (char)
| str  : String → Expr Δ Γ (string)
| var
  : {τ : Typ}
  → (x : Symbol)
  → Γ.syms x = .some (.var τ)
  → Expr Δ Γ τ
| «true»  : Expr Δ Γ (bool)
| «false» : Expr Δ Γ (bool)
| null    : Expr Δ Γ (any *)
| unop
  : (op : UnOp)
  → τ.equiv op.type
  → (e : Expr Δ Γ τ)
  → Expr Δ Γ op.type
| binop_int
  : {τ₁ : {τ : Typ // τ = (int)}}
  → {τ₂ : {τ : Typ // τ = (int)}}
  → (op : BinOp.Int)
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ (int)
| binop_bool
  : {τ₁ : {τ : Typ // τ = (bool)}}
  → {τ₂ : {τ : Typ // τ = (bool)}}
  → (op : BinOp.Bool)
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ (bool)
| binop_eq
  : (op : Comparator)
  → op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → τ₁.equiv τ₂
  → τ₁.is_eqtype ∨ τ₂.is_eqtype
  → Expr Δ Γ (bool)
| binop_rel₁
  : {τ₁ : {τ : Typ // τ = (int)}}
  → {τ₂ : {τ : Typ // τ = (int)}}
  → (op : Comparator)
  → ¬op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ (bool)
| binop_rel₂
  : {τ₁ : {τ : Typ // τ = (char)}}
  → {τ₂ : {τ : Typ // τ = (char)}}
  → (op : Comparator)
  → ¬op.isEquality
  → (l : Expr Δ Γ τ₁)
  → (r : Expr Δ Γ τ₂)
  → Expr Δ Γ (bool)
| ternop
  : {τ₁ : {τ : Typ // τ = (bool)}}
  → (cond : Expr Δ Γ τ₁)
  → (tt : Expr Δ Γ τ₂)
  → (ff : Expr Δ Γ τ₃)
  → τ₂.equiv τ₃
  → Expr Δ Γ (τ₂.intersect τ₃)
| app
  : (f : Symbol)
  → Γ.syms f = .some (.func status)
  → (τs : Fin status.type.arity → Typ)
  → (eq : ∀ i, (status.type.argTys i).equiv (τs i))
  → (args : (i : Fin status.type.arity) → Expr Δ Γ (τs i))
  → Expr Δ Γ status.type.retTy
| alloc : (τ : Typ) → Expr Δ Γ (τ*)
| alloc_array
  : {τ₁ : {τ : Typ // τ = (int)}}
  → (τ : Typ)
  → Expr Δ Γ τ₁
  → Expr Δ Γ (τ[])
| dot
  : {τ₁ : {τ : Typ // τ = (struct s)}}
  → Expr Δ Γ τ₁
  → (field : Symbol)
  → Δ.struct s = .some ⟨struct_fields, true⟩
  → struct_fields field = .some τ
  → Expr Δ Γ τ
| deref
  : {τ₁ : {τ' : Typ // τ' = (τ*)}}
  → Expr Δ Γ τ₁
  → Expr Δ Γ τ
| index
  : {τ₁ : {τ' : Typ // τ' = (τ[])}}
  → {τ₂ : {τ : Typ // τ = (int)}}
  → Expr Δ Γ τ₁
  → Expr Δ Γ τ₂
  → Expr Δ Γ τ
| result
  : Γ.ret = some τ
  → Expr Δ Γ τ
| length
  : {τ₁ : {τ' : Typ // τ' = (τ[])}}
  → Expr Δ Γ τ₁
  → Expr Δ Γ (int)

namespace Expr
open Typ.Notation

@[inline] def typeWith {p : Typ → Prop} (e : Expr Δ Γ τ) (h : p τ)
    : Expr Δ Γ (⟨τ, h⟩ : {τ : Typ // p τ}) := e
@[inline] def typeWithEq {τ₂ : Typ} (e : Expr Δ Γ τ) (eq : τ = τ₂)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = τ₂}) :=
  e.typeWith (p := fun t => t = τ₂) eq
@[inline] def typeWithEquiv {τ₂ : Typ} (e : Expr Δ Γ τ) (eq : τ.equiv τ₂)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ.equiv τ₂}) :=
  e.typeWith (p := fun t => t.equiv τ₂) eq


@[inline] def intType (e : Expr Δ Γ τ) (eq : τ = (int))
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (int)}) := e.typeWithEq eq
@[inline] def boolType (e : Expr Δ Γ τ) (eq : τ = (bool))
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (bool)}) := e.typeWithEq eq
@[inline] def charType (e : Expr Δ Γ τ) (eq : τ = .prim .char)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = .prim .char}) := e.typeWithEq eq
@[inline] def stringType (e : Expr Δ Γ τ) (eq : τ = .prim .string)
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = .prim .string}) := e.typeWithEq eq
@[inline] def ptrType (e : Expr Δ Γ τ) (τ' : Typ) (eq : τ = (τ'*))
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (τ'*)}) := e.typeWithEq eq
@[inline] def arrType (e : Expr Δ Γ τ) (τ' : Typ) (eq : τ = (τ'[]))
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (τ'[])}) := e.typeWithEq eq
@[inline] def structType (e : Expr Δ Γ τ) (s : Symbol) (eq : τ = (struct s))
    : Expr Δ Γ (⟨τ, eq⟩ : {τ : Typ // τ = (struct s)}) := e.typeWithEq eq

/- Assert that P can be folded to some value through every sub-expression -/
inductive Fold {Δ : GCtx} {Γ : FCtx}
    : (P : (τ : Typ) → α → Expr Δ Γ τ → Option α)
    → α → Expr Δ Γ τ → α → Prop
| num
  : {a₁ a₂ : α}
  → P _ a₁ (.num v) = some a₂
  → Fold P a₁ ((.num v) : Expr Δ Γ _) a₂
| char
  : {a₁ a₂ : α}
  → P _ a₁ (.char c) = some a₂
  → Fold P a₁ ((.char c) : Expr Δ Γ _) a₂
| str
  : {a₁ a₂ : α}
  → P _ a₁ (.str s) = some a₂
  → Fold P a₁ ((.str s) : Expr Δ Γ _) a₂
| var
  : {a₁ a₂ : α}
  → {h : Γ.syms x = .some (.var τ)}
  → P _ a₁ (.var x h) = some a₂
  → Fold P a₁ ((.var x h) : Expr Δ Γ _) a₂
| «true»
  : {a₁ a₂ : α}
  → P _ a₁ .true = some a₂
  → Fold P a₁ (.true : Expr Δ Γ _) a₂
| «false»
  : {a₁ a₂ : α}
  → P _ a₁ .false = some a₂
  → Fold P a₁ (.false : Expr Δ Γ _) a₂
| null
  : {a₁ a₂ : α}
  → P _ a₁ .null = some a₂
  → Fold P a₁ (.null : Expr Δ Γ _) a₂
| unop
  : {a₁ a₂ a₃ : α}
  → Fold P a₁ e a₂
  → P _ a₂ (.unop op eq e) = some a₃
  → Fold P a₁ (.unop op eq e) a₃
| binop_int
  : {a₁ a₂ a₃ a₄ : α}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_int op l r) = some a₄
  → Fold P a₁ (.binop_int op l r) a₄
| binop_bool
  : {a₁ a₂ a₃ a₄ : α}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_bool op l r) = some a₄
  → Fold P a₁ (.binop_bool op l r) a₄
| binop_eq
  : {a₁ a₂ a₃ a₄ : α}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_eq op eq l r h₁ h₂) = some a₄
  → Fold P a₁ (.binop_eq op eq l r h₁ h₂) a₄
| binop_rel₁
  : {a₁ a₂ a₃ a₄ : α}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_rel₁ op eq l r) = some a₄
  → Fold P a₁ (.binop_rel₁ op eq l r) a₄
| binop_rel₂
  : {a₁ a₂ a₃ a₄ : α}
  → Fold P a₁ l a₂
  → Fold P a₂ r a₃
  → P _ a₃ (.binop_rel₂ op eq l r) = some a₄
  → Fold P a₁ (.binop_rel₂ op eq l r) a₄
| ternop
  : {a₁ a₂ a₃ a₄ a₅ : α}
  → Fold P a₁ cc a₂
  → Fold P a₂ tt a₃
  → Fold P a₃ ff a₄
  → P _ a₄ (.ternop cc tt ff h₂) = some a₅
  → Fold P a₁ (.ternop cc tt ff h₂) a₅
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
  → Fold P a₁ e a₂
  → P _ a₂ (.alloc_array τ₁ e) = some a₃
  → Fold P a₁ (.alloc_array τ₁ e) a₃
| dot
  : {a₁ a₂ a₃ : α}
  → Fold P a₁ e a₂
  → P _ a₂ (.dot e f h₁ h₂) = some a₃
  → Fold P a₁ (.dot e f h₁ h₂) a₃
| deref
  : {a₁ a₂ a₃ : α}
  → Fold P a₁ e a₂
  → P _ a₂ (.deref e) = some a₃
  → Fold P a₁ (.deref e) a₃
| index
  : {a₁ a₂ a₃ : α}
  → Fold P a₁ e a₂
  → Fold P a₂ indx a₃
  → P _ a₃ (.index e indx) = some a₄
  → Fold P a₁ (.index e indx) a₄
| result
  : {a₁ a₂ : α}
  → P (τ := τ) a₁ (.result h) = some a₂
  → Fold P a₁ (.result h : Expr Δ Γ τ) a₂
| length
  : {a₁ a₂ a₃ : α}
  → Fold P a₁ e a₂
  → P _ a₂ (.length e) = some a₃
  → Fold P a₁ (.length e) a₃

def All (P : {τ : Typ} → Expr Δ Γ τ → Bool) (e : Expr Δ Γ τ) : Prop :=
  Expr.Fold (fun _ _ e => if P e then some () else none) () e ()

@[inline] def only_contract : Expr Δ Γ τ → Bool
  | .result _ => .true
  | .length _ => .true
  | _         => .false
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
  | plus => "+"
  | minus => "-"
  | times => "*"
  | div => "/"
  | mod => "%"
  | and => "&"
  | xor => "^"
  | or => "|"
  | lsh => "<<"
  | rsh => ">>"
instance : ToString BinOp.Int where toString := BinOp.Int.toString

def BinOp.Bool.toString : BinOp.Bool → String
  | .and => "&&"
  | .or  => "||"
instance : ToString BinOp.Bool where toString := BinOp.Bool.toString

def BinOp.toString : BinOp → String
  | int op  => s!"{op}"
  | cmp op  => s!"{op}"
  | bool op => s!"{op}"
instance : ToString BinOp where toString := BinOp.toString

def Expr.toString : Expr Δ Γ τ → String
  | .num v       => s!"({v} : {τ})"
  | .char c      => s!"('{c.toString.sanitise}' : {τ})"
  | .str s       => s!"(\"{s.sanitise}\" : {τ})"
  | .«true»      => s!"(true : {τ})"
  | .«false»     => s!"(false : {τ})"
  | .null        => s!"(NULL : {τ})"
  | .unop op _ e => s!"({op}{Expr.toString e} : {τ})"
  | .binop_int op l r
  | .binop_bool op l r
  | .binop_eq op _ l r _ _
  | .binop_rel₁ op _ l r
  | .binop_rel₂ op _ l r =>
    s!"({Expr.toString l} {op} {Expr.toString r} : {τ})"
  | .ternop cc tt ff _ =>
    s!"({Expr.toString cc} ? {Expr.toString tt} : {Expr.toString ff} : {τ})"
  | .app f _ _ _ args =>
    let str_args := ", ".intercalate
      (.ofFn (fun i => Expr.toString (args i)))
    s!"({f}({str_args}) : {τ})"
  | .alloc ty => s!"(alloc({ty}) : {τ})"
  | .alloc_array ty e => s!"(alloc_array({ty}, {Expr.toString e}) : {τ})"
  | .var name _ => s!"({name} : {τ})"
  | .dot e field _ _ => s!"({Expr.toString e}.{field} : {τ})"
  | .deref e   => s!"(*{Expr.toString e} : {τ})"
  | .index e i => s!"({Expr.toString e}[{Expr.toString i}] : {τ})"
  | .result _  => s!"(\\result : {τ})"
  | .length e  => s!"(\\length {Expr.toString e} : {τ})"

instance : ToString (Expr Δ Γ τ) := ⟨Expr.toString⟩
