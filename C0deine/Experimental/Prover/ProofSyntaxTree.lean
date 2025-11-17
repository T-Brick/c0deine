import Lean
import C0deine.Utils.Comparison
import C0deine.Context.Symbol
import C0deine.Type.Typ
import C0deine.Type.Tst
import Numbers

namespace C0deine.Pst

open Typ
open Numbers

inductive Expr
| num : Numbers.Int32 → Expr
| char : Char → Expr
| str : String → Expr
| var : Symbol → Expr
| «true» : Expr
| «false» : Expr
| null : Expr
| unop_int : Tst.UnOp.Int → Typed Expr → Expr
| unop_bool : Tst.UnOp.Bool → Typed Expr → Expr
| binop_int : Tst.BinOp.Int → Typed Expr → Typed Expr → Expr
| binop_bool : Tst.BinOp.Bool → Typed Expr → Typed Expr → Expr
| binop_eq : Comparator → Typed Expr → Typed Expr → Expr
| binop_rel_int : Comparator → Typed Expr → Typed Expr → Expr
| binop_rel_char : Comparator → Typed Expr → Typed Expr → Expr
| ternop : Typed Expr → Typed Expr → Typed Expr → Expr
| app : Symbol → List (Typed Expr) → Expr
| alloc : Typ → Expr
| alloc_array : Typ → Typed Expr → Expr
| dot : Typed Expr → Symbol → Expr
| deref : Typed Expr → Expr
| index : Typed Expr → Typed Expr → Expr
| result : Expr
| length : Typed Expr → Expr
deriving Inhabited, Lean.ToExpr

inductive LValue
| var : Symbol → LValue
| dot : Typed LValue → Symbol → LValue
| deref : Typed LValue → LValue
| index : Typed LValue → Typed Expr → LValue
deriving Inhabited, Lean.ToExpr

inductive Anno
| requires : Typed Expr → Anno
| ensures : Typed Expr → Anno
| loop_invar : Typed Expr → Anno
| assert : Typed Expr → Anno
deriving Inhabited, Lean.ToExpr

inductive Stmt
| decl : Typed Symbol → List Stmt → Stmt
| decl_init : Typed Symbol → Typed Expr → List Stmt → Stmt
| assign_var : Typed LValue → Typed Expr → Stmt
| assign : Typed LValue → Typed Expr → Stmt
| asnop : Typed LValue → Tst.BinOp.Int → Typed Expr → Stmt
| expr : Typed Expr → Stmt
| ite : Typed Expr → List Stmt → List Stmt → Stmt
| while : Typed Expr → List Anno → List Stmt → Stmt
| return_void : Stmt
| return_tau : Typed Expr → Stmt
| assert : Typed Expr → Stmt
| error : Typed Expr → Stmt
| anno : Anno → Stmt
deriving Inhabited, Lean.ToExpr

structure SDef where
  name : Symbol
  fields : List (Typed Symbol)
deriving Inhabited, Repr, Lean.ToExpr

structure FDecl where
  ret : Option Typ
  name : Symbol
  params : List (Typed Symbol)
  annos : List Anno
deriving Inhabited, Lean.ToExpr

structure FDef extends FDecl where
  body : List Stmt
deriving Inhabited, Lean.ToExpr

inductive GDecl
| fdecl : FDecl → GDecl
| fdef : FDef → GDecl
| sdef : SDef → GDecl
deriving Inhabited, Lean.ToExpr

structure Call where
  name : Symbol
  pure : Bool
deriving Inhabited, Repr, Lean.ToExpr

structure Prog where
  header : List GDecl
  body : List GDecl
  calls : List Call
  strings : List String
deriving Inhabited, Lean.ToExpr

def Expr.ofTst : Tst.Expr Δ Γ τ → Typed Expr
| .num _ i => ⟨τ, .num i⟩
| .char _ c => ⟨τ, .char c⟩
| .str _ s => ⟨τ, .str s⟩
| .var x _ => ⟨τ, .var x⟩
| .true _ => ⟨τ, .true⟩
| .false _ => ⟨τ, .false⟩
| .null _ => ⟨τ, .null⟩
| .unop_int _ _ op e => ⟨τ, .unop_int op (ofTst e)⟩
| .unop_bool _ _ op e => ⟨τ, .unop_bool op (ofTst e)⟩
| .binop_int _ _ _ op l r => ⟨τ, .binop_int op (ofTst l) (ofTst r)⟩
| .binop_bool _ _ _ op l r => ⟨τ, .binop_bool op (ofTst l) (ofTst r)⟩
| .binop_eq _ op _ l r _ _ => ⟨τ, .binop_eq op (ofTst l) (ofTst r)⟩
| .binop_rel_int _ _ _ op _ l r => ⟨τ, .binop_rel_int op (ofTst l) (ofTst r)⟩
| .binop_rel_char _ _ _ op _ l r => ⟨τ, .binop_rel_char op (ofTst l) (ofTst r)⟩
| .ternop _ _ c t f _ => ⟨τ, .ternop (ofTst c) (ofTst t) (ofTst f)⟩
| .app (status:=status) f _ _ _ args =>
    panic! "Currently, cannot convert function call"
| .alloc τ' => ⟨τ, .alloc τ'⟩
| .alloc_array _ τ' e => ⟨τ, .alloc_array τ' (ofTst e)⟩
| .dot _ e f _ _ => ⟨τ, .dot (ofTst e) f⟩
| .deref _ e => ⟨τ, .deref (ofTst e)⟩
| .index _ _ a i => ⟨τ, .index (ofTst a) (ofTst i)⟩
| .result _ => ⟨τ, .result⟩
| .length _ e => ⟨τ, .length (ofTst e)⟩

def LValue.ofTst : Tst.LValue Δ Γ τ → Typed LValue
| .var x _ => ⟨τ, .var x⟩
| .dot _ lv field _ _ => ⟨τ, .dot (LValue.ofTst lv) field⟩
| .deref _ lv => ⟨τ, .deref (LValue.ofTst lv)⟩
| .index _ _ a i => ⟨τ, .index (LValue.ofTst a) (Expr.ofTst i.val)⟩

def Anno.ofTst : Tst.Anno Δ Γ → Anno
| .requires _ e   => .requires (Expr.ofTst e.val)
| .ensures _ e    => .ensures (Expr.ofTst e)
| .loop_invar _ e => .loop_invar (Expr.ofTst e.val)
| .assert _ e     => .assert (Expr.ofTst e.val)

partial def Stmt.ofTst : Tst.Stmt Δ Γ ρ → Stmt
| .decl name _ body => .decl name (body.toList.map (Stmt.ofTst))
| .decl_init name init _ _ body => .decl_init name (Expr.ofTst init.val) (body.toList.map (Stmt.ofTst))
| .assign_var l _ r _ => .assign_var (LValue.ofTst l) (Expr.ofTst r.val)
| .assign l _ r _ => .assign (LValue.ofTst l) (Expr.ofTst r.val)
| .asnop _ _ l op r => .asnop (LValue.ofTst l) op (Expr.ofTst r.val)
| .expr e => .expr (Expr.ofTst e.val)
| .ite _ c t f => .ite (Expr.ofTst c.val) (t.toList.map (Stmt.ofTst)) (f.toList.map (Stmt.ofTst))
| .while _ c annos body => .while (Expr.ofTst c.val) (annos.map (Anno.ofTst ·.val)) (body.toList.map (Stmt.ofTst))
| .return_void _ => .return_void
| .return_tau _ e => .return_tau (Expr.ofTst e.val)
| .assert _ e => .assert (Expr.ofTst e.val)
| .error _ e => .error (Expr.ofTst e.val)
| .anno a => .anno (Anno.ofTst a.val)

def SDef.ofTst : Tst.SDef → SDef
| ⟨name, field⟩ => ⟨name, field⟩

set_option linter.unusedVariables false in
def FDecl.ofTst : Tst.FDecl Δ → FDecl
| {ret, name, params, init_Γ, annos, initial_init, annos_init} =>
    { ret, name, params, annos := annos.map (Anno.ofTst ·.val)}

set_option linter.unusedVariables false in
def FDef.ofTst : Tst.FDef Δ → FDef
| {ret, name, params, init_Γ, annos, initial_init, annos_init, body, post_init, body_init, body_rets} =>
    { ret, name, params,
      annos := annos.map (Anno.ofTst ·.val),
      body := body.toList.map (Stmt.ofTst)
    }

def Gdecl.ofTst : Tst.GDecl Δ₁ Δ₂ → GDecl
| .fdecl f => .fdecl (FDecl.ofTst f)
| .fdef f => .fdef (FDef.ofTst f)
| .sdef s => .sdef (SDef.ofTst s)


mutual
partial def Expr.toString : Expr → String
| .num i => s!"{i}"
| .char c => s!"'${c}'"
| .str s => s!"\"${s}\""
| .var x => s!"{x}"
| .«true» => "true"
| .«false» => "false"
| .null => "null"
| .unop_int op i => s!"{op} {typedToString i}"
| .unop_bool op b => s!"{op} {typedToString b}"
| .binop_int op l r => s!"{typedToString l} {op} {typedToString r}"
| .binop_bool op l r => s!"{typedToString l} {op} {typedToString r}"
| .binop_eq op l r => s!"{typedToString l} {op} {typedToString r}"
| .binop_rel_int op l r => s!"{typedToString l} {op} {typedToString r}"
| .binop_rel_char op l r => s!"{typedToString l} {op} {typedToString r}"
| .ternop c t f => s!"{typedToString c} ? {typedToString t} : {typedToString f}"
| .app f args => s!"{f}({args.map typedToString |>.concat ", "})"
| .alloc τ => s!"alloc({τ})"
| .alloc_array τ i => s!"alloc_array({τ}, {typedToString i})"
| .dot e f => s!"{typedToString e}.{f}"
| .deref e => s!"{typedToString e}"
| .index a i => s!"{typedToString a}[{typedToString i}]"
| .result => s!"\\result"
| .length e => s!"\\length({typedToString e})"

partial def Expr.typedToString (texpr : Typed Expr) : String :=
  s!"({Expr.toString texpr.data} : {texpr.type})"
end

instance : ToString Expr := ⟨Expr.toString⟩
instance : ToString (Typed Expr) := ⟨Expr.typedToString⟩
instance : Repr Expr := ⟨fun e _ => Expr.toString e⟩
instance : Repr (Typed Expr) := ⟨fun te _ => Expr.typedToString te⟩

namespace Notation

declare_syntax_cat c0_symbol
scoped syntax ident "#" num : c0_symbol
scoped syntax "c0_symbol% " c0_symbol : term

declare_syntax_cat c0_type
syntax "int"                : c0_type
syntax "bool"               : c0_type
syntax "char"               : c0_type
syntax "string"             : c0_type
syntax "any"                : c0_type
syntax "any" " *"           : c0_type
syntax c0_type " *"         : c0_type
syntax c0_type "[]"         : c0_type
syntax "struct" c0_symbol   : c0_type
syntax "c0_type% " c0_type  : term

declare_syntax_cat c0_tsymbol -- typed symbol, used in decls
scoped syntax:40 c0_symbol:40 " :ₛ " c0_type:41 : c0_tsymbol
scoped syntax:40 "(" c0_tsymbol ")" : c0_tsymbol
scoped syntax "c0_tsymbol% " c0_tsymbol : term

declare_syntax_cat c0_expr
declare_syntax_cat c0_texpr
declare_syntax_cat c0_args

/- TODO: make the precedences make sense -/
scoped syntax "(" c0_expr ")" : c0_expr
scoped syntax num : c0_expr
scoped syntax Lean.Parser.charLit : c0_expr
scoped syntax str : c0_expr
scoped syntax c0_symbol : c0_expr
scoped syntax "true" : c0_expr
scoped syntax "false" : c0_expr
scoped syntax "null" : c0_expr
scoped syntax:20 "~" c0_texpr:20 : c0_expr
scoped syntax:20 "-" c0_texpr:20 : c0_expr
scoped syntax:20 "!" c0_texpr:20 : c0_expr
scoped syntax:30 c0_texpr:30 " + " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " - " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " * " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " / " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " % " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " & " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " | " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " ^ " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " << " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " >> " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " && " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " || " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " == " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " != " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " <ᵢ " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " <=ᵢ " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " >ᵢ " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " >=ᵢ " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " < " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " <= " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " > " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:30 " >= " c0_texpr:31 : c0_expr
scoped syntax:30 c0_texpr:31 " ? " c0_texpr:31 " : " c0_texpr:31 : c0_expr
scoped syntax c0_symbol "(-)" : c0_expr
scoped syntax c0_symbol "(" c0_args ")" : c0_expr
scoped syntax "alloc(" c0_type ")" : c0_expr
scoped syntax "alloc_array(" c0_type ", " c0_texpr ")" : c0_expr
scoped syntax:30 c0_texpr:30 "." c0_symbol : c0_expr
scoped syntax:20 "*" c0_texpr:20 : c0_expr
scoped syntax:30 c0_texpr:30 "[" c0_texpr:31 "]" : c0_expr
scoped syntax "\\result" : c0_expr
scoped syntax "\\length " c0_texpr : c0_expr

scoped syntax:40 c0_expr:40 " : " c0_type:41 : c0_texpr
scoped syntax:40 "(" c0_texpr ")" : c0_texpr

scoped syntax c0_texpr : c0_args
scoped syntax c0_texpr ", " c0_args : c0_args

scoped syntax ">>c0_expr| " c0_expr " <<" : term
scoped syntax ">>c0_texpr| " c0_texpr " <<" : term
scoped syntax ">>c0_args| " c0_args " <<" : term

macro_rules
| `(c0_symbol% $x:ident # $n:num) => `(Symbol.mk $(Lean.quote (toString x.getId)) $n)

macro_rules
| `(c0_type% int)                 => `(Typ.prim Typ.Primitive.int)
| `(c0_type% bool)                => `(Typ.prim Typ.Primitive.bool)
| `(c0_type% char)                => `(Typ.prim Typ.Primitive.char)
| `(c0_type% string)              => `(Typ.prim Typ.Primitive.string)
| `(c0_type% any)                 => `(Typ.any)
| `(c0_type% any*)                => `(Typ.mem (Typ.Memory.pointer Typ.any))
| `(c0_type% $τ:c0_type*)         => `(Typ.mem (Typ.Memory.pointer (c0_type% $τ)))
| `(c0_type% $τ:c0_type[])        => `(Typ.mem (Typ.Memory.array (c0_type% $τ)))
| `(c0_type% struct $s:c0_symbol) => `(Typ.mem (Typ.Memory.struct (c0_symbol% $s)))

macro_rules
| `(c0_tsymbol% $x:c0_symbol :ₛ $τ) => `(Typ.Typed.mk (c0_type% $τ) (c0_symbol% $x))
| `(c0_tsymbol% ($x:c0_tsymbol))    => `(c0_tsymbol% $x)

macro_rules
| `(>>c0_expr| ($e:c0_expr)<<)            => `(>>c0_expr| $e <<)
| `(>>c0_expr| $n:num <<)                 => `(Expr.num $n)
| `(>>c0_expr| $c:char <<)                => `(Expr.char $c)
| `(>>c0_expr| $s:str <<)                 => `(Expr.str $s)
| `(>>c0_expr| $x:c0_symbol <<)           => `(Expr.var (c0_symbol% $x))
| `(>>c0_expr| true <<)                   => `(Expr.true)
| `(>>c0_expr| false <<)                  => `(Expr.false)
| `(>>c0_expr| null <<)                   => `(Expr.null)
| `(>>c0_expr| ~ $e <<)                   => `(Expr.unop_int .not >>c0_texpr| $e <<)
| `(>>c0_expr| - $e <<)                   => `(Expr.unop_int .neg >>c0_texpr| $e <<)
| `(>>c0_expr| ! $e <<)                   => `(Expr.unop_bool .neg >>c0_texpr| $e <<)
| `(>>c0_expr| $l:c0_texpr + $r <<)       => `(Expr.binop_int .plus >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr - $r <<)       => `(Expr.binop_int .minus >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr * $r <<)       => `(Expr.binop_int .times >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr / $r <<)       => `(Expr.binop_int .div >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr % $r <<)       => `(Expr.binop_int .mod >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr & $r <<)       => `(Expr.binop_int .and >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr | $r <<)       => `(Expr.binop_int .or >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr ^ $r <<)       => `(Expr.binop_int .xor >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr << $r <<)      => `(Expr.binop_int .lsh >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr >> $r <<)      => `(Expr.binop_int .rsh >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr && $r <<)      => `(Expr.binop_bool .and >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr || $r <<)      => `(Expr.binop_bool .or >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr == $r <<)      => `(Expr.binop_eq .equal >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr != $r <<)      => `(Expr.binop_eq .not_equal >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr <ᵢ $r <<)      => `(Expr.binop_rel_int .less >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr <=ᵢ $r <<)     => `(Expr.binop_rel_int .less_equal >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr >ᵢ $r <<)      => `(Expr.binop_rel_int .greater >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr >=ᵢ $r <<)     => `(Expr.binop_rel_int .greater_equal >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr < $r <<)       => `(Expr.binop_rel_char .less >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr <= $r <<)      => `(Expr.binop_rel_char .less_equal >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr > $r <<)       => `(Expr.binop_rel_char .greater >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $l:c0_texpr >= $r <<)      => `(Expr.binop_rel_char .greater_equal >>c0_texpr| $l << >>c0_texpr| $r <<)
| `(>>c0_expr| $c:c0_texpr ? $t : $f <<)  => `(Expr.ternop >>c0_texpr| $c << >>c0_texpr| $t << >>c0_texpr| $f <<)
| `(>>c0_expr| $f:c0_symbol(-) <<)        => `(Expr.app (c0_symbol% $f) .nil)
| `(>>c0_expr| $f:c0_symbol($args) <<)    => `(Expr.app (c0_symbol% $f) (>>c0_args| $args <<).reverse)
| `(>>c0_expr| alloc($τ) <<)              => `(Expr.alloc (c0_type% $τ))
| `(>>c0_expr| alloc_array($τ, $e) <<)    => `(Expr.alloc_array (c0_type% $τ) >>c0_texpr| $e <<)
| `(>>c0_expr| $e:c0_texpr . $f <<)       => `(Expr.dot >>c0_texpr| $e << (c0_symbol% $f))
| `(>>c0_expr| * $e <<)                   => `(Expr.deref >>c0_texpr| $e <<)
| `(>>c0_expr| $a:c0_texpr[$i] <<)        => `(Expr.index >>c0_texpr| $a << >>c0_texpr| $i <<)
| `(>>c0_expr| \result <<)                => `(Expr.result)
| `(>>c0_expr| \length $e <<)             => `(Expr.length >>c0_texpr| $e <<)

macro_rules
| `(>>c0_texpr| $e:c0_expr : $τ:c0_type <<) => `(Typ.Typed.mk (c0_type% $τ) >>c0_expr| $e <<)
| `(>>c0_texpr| ($e:c0_texpr) <<) => `(>>c0_texpr| $e <<)

macro_rules
| `(>>c0_args| $e:c0_texpr <<)                => `(List.cons >>c0_texpr| $e << .nil)
| `(>>c0_args| $e:c0_texpr, $args:c0_args <<) => `(List.cons >>c0_texpr| $e << >>c0_args| $args <<)

@[app_unexpander Symbol.mk]
def unexpandSymbol : Lean.PrettyPrinter.Unexpander
| `($_ $x:str $n:num) =>
  let str := x.getString
  let name := Lean.mkIdent $ Lean.Name.mkSimple str
  `(c0_symbol% $name:ident # $n)
| _ => throw ()

@[inline]
def unexpandC0SymbolUtil
    (k : Lean.TSyntax `c0_symbol → Lean.PrettyPrinter.UnexpandM Lean.Syntax)
    : Lean.TSyntax `term → Lean.PrettyPrinter.UnexpandM Lean.Syntax
| `(c0_symbol% $x) | `((c0_symbol% $x)) => k x
| _ => throw ()

@[app_unexpander Typ.any]
def unexpandTypAny : Lean.PrettyPrinter.Unexpander
| `($_) => `((c0_type% any))

@[app_unexpander Typ.prim]
def unexpandTypPrim : Lean.PrettyPrinter.Unexpander
| `($_ $τ) =>
  match τ.raw.getId with
  | `Primitive.int    | `Typ.Primitive.int    => `((c0_type% int))
  | `Primitive.bool   | `Typ.Primitive.bool   => `((c0_type% bool))
  | `Primitive.char   | `Typ.Primitive.char   => `((c0_type% char))
  | `Primitive.string | `Typ.Primitive.string => `((c0_type% string))
  | _ => throw ()
| _ => throw ()

@[app_unexpander Typ.Memory.pointer]
def unexpandTypMemPointer : Lean.PrettyPrinter.Unexpander
| `($_ (c0_type% $τ)) => `((c0_type% $τ *))
| _ => throw ()

@[app_unexpander Typ.Memory.array]
def unexpandTypMemArray : Lean.PrettyPrinter.Unexpander
| `($_ (c0_type% $τ)) => `((c0_type% $τ[]))
| _ => throw ()

@[app_unexpander Typ.Memory.struct]
def unexpandTypMemStruct: Lean.PrettyPrinter.Unexpander
| `($_ $s) => unexpandC0SymbolUtil (fun s => `(c0_type% struct $s)) s
| _ => throw ()

@[app_unexpander Typ.mem]
def unexpandTypMem : Lean.PrettyPrinter.Unexpander
| `($_ (c0_type% $τ)) => `((c0_type% $τ))
| _ => throw ()

@[app_unexpander Typ.Typed.mk]
def unexpandTyped : Lean.PrettyPrinter.Unexpander
| `($_ (c0_type% $τ) >>c0_expr| $e <<) =>
    `(>>c0_texpr| $e:c0_expr : $τ:c0_type <<)
| `($_ (c0_type% $τ) $x) =>
    unexpandC0SymbolUtil (fun y => `(c0_tsymbol% $y:c0_symbol :ₛ $τ)) x
| _ => throw ()

@[app_unexpander Expr.num]
def unexpandNum : Lean.PrettyPrinter.Unexpander
| `($_ $x:num) => `(>>c0_expr| $x:num <<)
| _ => throw ()

@[app_unexpander Expr.char]
def unexpandChar : Lean.PrettyPrinter.Unexpander
| `($_ $c:char) => `(>>c0_expr| $c:char <<)
| _ => throw ()

@[app_unexpander Expr.str]
def unexpandStr : Lean.PrettyPrinter.Unexpander
| `($_ $s:str) => `(>>c0_expr| $s:str <<)
| _ => throw ()

@[app_unexpander Expr.var]
def unexpandVar : Lean.PrettyPrinter.Unexpander
| `($_ $x) => unexpandC0SymbolUtil (fun y => `(>>c0_expr| $y:c0_symbol <<)) x
| _ => throw ()

@[app_unexpander Expr.true]
def unexpandTrue : Lean.PrettyPrinter.Unexpander
| `($_) => `(>>c0_expr| true <<)

@[app_unexpander Expr.false]
def unexpandFalse : Lean.PrettyPrinter.Unexpander
| `($_) => `(>>c0_expr| false <<)

@[app_unexpander Expr.null]
def unexpandNull : Lean.PrettyPrinter.Unexpander
| `($_) => `(>>c0_expr| null <<)

@[app_unexpander Expr.unop_int]
def unexpandUnopInt : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $e <<) =>
  match op.raw.getId with
  | `Tst.UnOp.Int.not => `(>>c0_expr| ~ $e <<)
  | `Tst.UnOp.Int.neg => `(>>c0_expr| - $e <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.unop_bool]
def unexpandUnopBool : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $e <<) =>
  match op.raw.getId with
  | `Tst.UnOp.Bool.neg => `(>>c0_expr| ! $e <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.binop_int]
def unexpandBinopInt : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $l << >>c0_texpr| $r <<) =>
  match op.raw.getId with
  | `Tst.BinOp.Int.plus   => `(>>c0_expr| ($l:c0_texpr + $r) <<)
  | `Tst.BinOp.Int.minus  => `(>>c0_expr| ($l:c0_texpr - $r) <<)
  | `Tst.BinOp.Int.times  => `(>>c0_expr| ($l:c0_texpr * $r) <<)
  | `Tst.BinOp.Int.div    => `(>>c0_expr| ($l:c0_texpr / $r) <<)
  | `Tst.BinOp.Int.mod    => `(>>c0_expr| ($l:c0_texpr % $r) <<)
  | `Tst.BinOp.Int.and    => `(>>c0_expr| ($l:c0_texpr & $r) <<)
  | `Tst.BinOp.Int.xor    => `(>>c0_expr| ($l:c0_texpr ^ $r) <<)
  | `Tst.BinOp.Int.or     => `(>>c0_expr| ($l:c0_texpr | $r) <<)
  | `Tst.BinOp.Int.lsh    => `(>>c0_expr| ($l:c0_texpr << $r) <<)
  | `Tst.BinOp.Int.rsh    => `(>>c0_expr| ($l:c0_texpr >> $r) <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.binop_bool]
def unexpandBinopBool : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $l << >>c0_texpr| $r <<) =>
  match op.raw.getId with
  | `Tst.BinOp.Bool.and => `(>>c0_expr| ($l:c0_texpr && $r) <<)
  | `Tst.BinOp.Bool.or  => `(>>c0_expr| ($l:c0_texpr || $r) <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.binop_eq]
def unexpandBinopEq : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $l << >>c0_texpr| $r <<) =>
  match op.raw.getId with
  | `Comparator.equal     => `(>>c0_expr| ($l:c0_texpr == $r) <<)
  | `Comparator.not_equal => `(>>c0_expr| ($l:c0_texpr != $r) <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.binop_rel_int]
def unexpandBinopRelInt : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $l << >>c0_texpr| $r <<) =>
  match op.raw.getId with
  | `Comparator.less          => `(>>c0_expr| ($l:c0_texpr <ᵢ $r) <<)
  | `Comparator.less_equal    => `(>>c0_expr| ($l:c0_texpr <=ᵢ $r) <<)
  | `Comparator.greater       => `(>>c0_expr| ($l:c0_texpr >ᵢ $r) <<)
  | `Comparator.greater_equal => `(>>c0_expr| ($l:c0_texpr >=ᵢ $r) <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.binop_rel_char]
def unexpandBinopRelChar : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $l << >>c0_texpr| $r <<) =>
  match op.raw.getId with
  | `Comparator.less          => `(>>c0_expr| ($l:c0_texpr < $r) <<)
  | `Comparator.less_equal    => `(>>c0_expr| ($l:c0_texpr <= $r) <<)
  | `Comparator.greater       => `(>>c0_expr| ($l:c0_texpr > $r) <<)
  | `Comparator.greater_equal => `(>>c0_expr| ($l:c0_texpr >= $r) <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.ternop]
def unexpandTernop : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $c << >>c0_texpr| $t << >>c0_texpr| $f <<) =>
    `(>>c0_expr| ($c:c0_texpr ? $t : $f) <<)
| _ => throw ()

@[app_unexpander Expr.app]
def unexpandApp : Lean.PrettyPrinter.Unexpander
| `($_ $f [ ]) => unexpandC0SymbolUtil (fun f => `(>>c0_expr| $f:c0_symbol(-) <<)) f
-- | `($_ $f $args) => unexpandC0SymbolUtil (fun f => `(>>c0_expr| $f:c0_symbol(-) <<)) f
| _ => throw ()
-- todo function app

@[app_unexpander Expr.alloc]
def unexpandAlloc : Lean.PrettyPrinter.Unexpander
| `($_ (c0_type% $τ)) => `(>>c0_expr| alloc($τ) <<)
| _ => throw ()

@[app_unexpander Expr.alloc_array]
def unexpandAllocArray : Lean.PrettyPrinter.Unexpander
| `($_ (c0_type% $τ) >>c0_texpr| $e <<) =>
    `(>>c0_expr| alloc_array($τ, $e) <<)
| _ => throw ()

@[app_unexpander Expr.dot]
def unexpandDot : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e << $f) =>
    unexpandC0SymbolUtil (fun f => `(>>c0_expr| $e:c0_texpr. $f<<)) f
| _ => throw ()

@[app_unexpander Expr.deref]
def unexpandDeref : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_expr| *$e <<)
| _ => throw ()

@[app_unexpander Expr.index]
def unexpandIndex : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $a << >>c0_texpr| $i <<) =>
    `(>>c0_expr| $a:c0_texpr[$i] <<)
| _ => throw ()

@[app_unexpander Expr.result]
def unexpandResult : Lean.PrettyPrinter.Unexpander
| `($_) => `(>>c0_expr| \result <<)

@[app_unexpander Expr.length]
def unexpandLength : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_expr| *$e <<)
| _ => throw ()

#check >>c0_texpr| (x#5 : int + 5 : int) : int <<
#check >>c0_expr| (5 : int) >= (5 : int) <<
#check >>c0_expr| f#0(x#1:int) <<

#check Typ.Typed.mk (c0_type% int) (c0_symbol% x#1)
#check Expr.app ⟨"f", 0⟩ .nil

#check Pst.Expr.binop_int Tst.BinOp.Int.plus (Typ.Typed.mk (Typ.prim Typ.Primitive.int) (Pst.Expr.num 100))
          (Typ.Typed.mk (Typ.prim Typ.Primitive.int) (Pst.Expr.num 50))
