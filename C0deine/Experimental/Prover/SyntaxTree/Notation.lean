import C0deine.Experimental.Prover.SyntaxTree.Pst

namespace C0deine.Pst.Notation

declare_syntax_cat c0_symbol
scoped syntax ident : c0_symbol
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

declare_syntax_cat c0_binop_int
scoped syntax " + "  : c0_binop_int
scoped syntax " - "  : c0_binop_int
scoped syntax " * "  : c0_binop_int
scoped syntax " / "  : c0_binop_int
scoped syntax " % "  : c0_binop_int
scoped syntax " & "  : c0_binop_int
scoped syntax " | "  : c0_binop_int
scoped syntax " ^ "  : c0_binop_int
scoped syntax " >> " : c0_binop_int
scoped syntax " << " : c0_binop_int

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
scoped syntax:30 c0_texpr:30 c0_binop_int c0_texpr:31 : c0_expr
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
scoped syntax:40 "*" c0_texpr:40 : c0_expr
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

declare_syntax_cat c0_lvalue
declare_syntax_cat c0_tlvalue

scoped syntax "(" c0_lvalue ")" : c0_lvalue
scoped syntax c0_symbol : c0_lvalue
scoped syntax:30 c0_tlvalue:30 "." c0_symbol : c0_lvalue
scoped syntax:20 "*" c0_tlvalue:20 : c0_lvalue
scoped syntax:30 c0_tlvalue:30 "[" c0_texpr:31 "]" : c0_lvalue

scoped syntax:40 c0_lvalue:40 " : " c0_type:41 : c0_tlvalue
scoped syntax:40 "(" c0_tlvalue ")" : c0_tlvalue

scoped syntax ">>c0_lvalue| " c0_lvalue " <<" : term
scoped syntax ">>c0_tlvalue| " c0_tlvalue " <<" : term

declare_syntax_cat c0_anno

scoped syntax "//@requires " c0_texpr       : c0_anno
scoped syntax "//@ensures " c0_texpr        : c0_anno
scoped syntax "//@loop_invariant " c0_texpr : c0_anno
scoped syntax "//@assert " c0_texpr         : c0_anno

scoped syntax ">>c0_anno| " c0_anno " <<" : term
scoped syntax ">>c0_annos| " sepBy(c0_anno, ";\n") " <<" : term

declare_syntax_cat c0_stmt
declare_syntax_cat c0_stmts

scoped syntax:40 c0_type:40 c0_symbol:41 c0_stmts:41 : c0_stmt
scoped syntax:10 c0_type:10 c0_symbol:11 " = " c0_texpr:12 c0_stmts:12 : c0_stmt
scoped syntax:40 c0_tlvalue:40 " = " c0_texpr:41 : c0_stmt
scoped syntax:40 c0_tlvalue:40 c0_binop_int:41 noWs "= " c0_texpr:41 : c0_stmt
scoped syntax c0_texpr : c0_stmt
scoped syntax "if(" c0_texpr ") " c0_stmts "else " c0_stmts : c0_stmt
scoped syntax "while(" c0_texpr ")\n" sepBy(c0_anno, ";\n") c0_stmts : c0_stmt
scoped syntax "return" : c0_stmt
scoped syntax "return " c0_texpr : c0_stmt
scoped syntax "assert(" c0_texpr ")" : c0_stmt
scoped syntax "error(" c0_texpr ")" : c0_stmt
scoped syntax c0_anno : c0_stmt

scoped syntax " {\n" sepBy(c0_stmt, ";\n") "\n} " : c0_stmts

scoped syntax ">>c0_stmt| " c0_stmt " <<" : term
scoped syntax ">>c0_stmts| " c0_stmts " <<" : term

macro_rules
| `(c0_symbol% $ident:ident) =>
  let identStr := toString ident.getId
  let id := identStr.dropWhile (¬·.isSubscriptNat) |> Nat.ofSubscriptString!
  let x := identStr.takeWhile (¬·.isSubscriptNat)
  `(Symbol.mk $(Lean.quote x) $(Lean.quote id))

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

/-
  Expr Macros
-/
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
| `(>>c0_texpr| ($e:c0_texpr) <<)           => `(>>c0_texpr| $e <<)

macro_rules
| `(>>c0_args| $e:c0_texpr <<)                => `(List.cons >>c0_texpr| $e << .nil)
| `(>>c0_args| $e:c0_texpr, $args:c0_args <<) => `(List.cons >>c0_texpr| $e << >>c0_args| $args <<)

/-
  LValue Macros
-/
macro_rules
| `(>>c0_lvalue| ($l:c0_lvalue) <<)     => `(>>c0_lvalue| $l <<)
| `(>>c0_lvalue| $x:c0_symbol <<)       => `(LValue.var (c0_symbol% $x))
| `(>>c0_lvalue| $l:c0_tlvalue . $f <<) => `(LValue.dot >>c0_tlvalue| $l << (c0_symbol% $f))
| `(>>c0_lvalue| * $l <<)               => `(LValue.deref >>c0_tlvalue| $l <<)
| `(>>c0_lvalue| $a:c0_tlvalue[$i] <<)  => `(LValue.index >>c0_tlvalue| $a << >>c0_texpr| $i <<)

macro_rules
| `(>>c0_tlvalue| $e:c0_lvalue : $τ:c0_type <<) => `(Typ.Typed.mk (c0_type% $τ) >>c0_lvalue| $e <<)
| `(>>c0_tlvalue| ($e:c0_tlvalue) <<)           => `(>>c0_tlvalue| $e <<)

/-
  Annotation Macros
-/
macro_rules
| `(>>c0_anno| //@requires $e:c0_texpr <<)       => `(Anno.requires >>c0_texpr| $e <<)
| `(>>c0_anno| //@ensures $e:c0_texpr <<)        => `(Anno.ensures >>c0_texpr| $e <<)
| `(>>c0_anno| //@loop_invariant $e:c0_texpr <<) => `(Anno.loop_invar >>c0_texpr| $e <<)
| `(>>c0_anno| //@assert $e:c0_texpr <<)         => `(Anno.assert >>c0_texpr| $e <<)

macro_rules
| `(>>c0_annos| <<) => `(.nil)
| `(>>c0_annos| $a:c0_anno; $annos;* <<) =>
    `(.cons >>c0_anno| $a << >>c0_annos| $annos;* <<)

/-
  Statements Macros
-/
macro_rules
| `(>>c0_stmts| { } <<) => `(.nil)
| `(>>c0_stmts| { $s:c0_stmt } <<) => `(.cons >>c0_stmt| $s << .nil)
| `(>>c0_stmts| { $s:c0_stmt; $ss:c0_stmt;* } <<) =>
    `(.cons >>c0_stmt| $s << >>c0_stmts| { $ss:c0_stmt;* } <<)

-- " + "
-- " - "
-- " * "
-- " / "
-- " % "
-- " & "
-- " | "
-- " ^ "

macro_rules
| `(>>c0_stmt| $τ:c0_type $x:c0_symbol $ss:c0_stmts <<) =>
    `(Stmt.decl (Typ.Typed.mk (c0_type% $τ) (c0_symbol% $x)) >>c0_stmts| $ss <<)
| `(>>c0_stmt| $τ:c0_type $x = $e $ss:c0_stmts <<) =>
    `(Stmt.decl_init (Typ.Typed.mk (c0_type% $τ) (c0_symbol% $x)) >>c0_texpr| $e << >>c0_stmts| $ss <<)
| `(>>c0_stmt| $x:c0_symbol : $τ = $e <<) =>
    `(Stmt.assign_var (Typ.Typed.mk (c0_type% $τ) (LValue.var (c0_symbol% $x))) >>c0_texpr| $e <<)
| `(>>c0_stmt| $l:c0_tlvalue = $e <<) =>
    `(Stmt.assign_var >>c0_tlvalue| $l << >>c0_texpr| $e <<)
| `(>>c0_stmt| $l:c0_tlvalue += $e <<) =>
    `(Stmt.asnop >>c0_tlvalue| $l << .plus >>c0_texpr| $e <<)
| `(>>c0_stmt| $l:c0_tlvalue -= $e <<) =>
    `(Stmt.asnop >>c0_tlvalue| $l << .minus >>c0_texpr| $e <<)
| `(>>c0_stmt| $l:c0_tlvalue *= $e <<) =>
    `(Stmt.asnop >>c0_tlvalue| $l << .times >>c0_texpr| $e <<)
| `(>>c0_stmt| $l:c0_tlvalue /= $e <<) =>
    `(Stmt.asnop >>c0_tlvalue| $l << .div >>c0_texpr| $e <<)
| `(>>c0_stmt| $l:c0_tlvalue %= $e <<) =>
    `(Stmt.asnop >>c0_tlvalue| $l << .mod >>c0_texpr| $e <<)
| `(>>c0_stmt| $l:c0_tlvalue &= $e <<) =>
    `(Stmt.asnop >>c0_tlvalue| $l << .and >>c0_texpr| $e <<)
| `(>>c0_stmt| $l:c0_tlvalue |= $e <<) =>
    `(Stmt.asnop >>c0_tlvalue| $l << .or >>c0_texpr| $e <<)
| `(>>c0_stmt| $l:c0_tlvalue ^= $e <<) =>
    `(Stmt.asnop >>c0_tlvalue| $l << .xor >>c0_texpr| $e <<)
| `(>>c0_stmt| $l:c0_tlvalue <<= $e <<) =>
    `(Stmt.asnop >>c0_tlvalue| $l << .lsh >>c0_texpr| $e <<)
| `(>>c0_stmt| $l:c0_tlvalue $_= $e:c0_texpr <<) =>
    `(Stmt.asnop >>c0_tlvalue| $l << .rsh >>c0_texpr| $e <<)
| `(>>c0_stmt| $e:c0_texpr <<) => `(Stmt.expr >>c0_texpr| $e <<)
| `(>>c0_stmt| if($e) $t else $f <<) =>
    `(Stmt.ite >>c0_texpr| $e << >>c0_stmts| $t << >>c0_stmts| $f <<)
| `(>>c0_stmt| while($c) $annos:c0_anno;* $body:c0_stmts <<) =>
    `(Stmt.while >>c0_texpr| $c << >>c0_annos| $annos;* << >>c0_stmts| $body <<)
| `(>>c0_stmt| return <<) => `(Stmt.return_void)
| `(>>c0_stmt| return $e <<) => `(Stmt.return_tau >>c0_texpr| $e <<)
| `(>>c0_stmt| assert($e) <<) => `(Stmt.assert >>c0_texpr| $e <<)
| `(>>c0_stmt| error($e) <<) => `(Stmt.error >>c0_texpr| $e <<)
| `(>>c0_stmt| $a:c0_anno <<) => `(Stmt.anno >>c0_anno| $a <<)

@[app_unexpander Symbol.mk]
def unexpandSymbol : Lean.PrettyPrinter.Unexpander
| `($_ $x:str $n:num) =>
  let str := s!"{x.getString}{n.getNat.toSubscriptString}"
  let name := Lean.mkIdent $ Lean.Name.mkSimple str
  `(c0_symbol% $name:ident)
| _ => throw ()

@[inline]
partial def unexpandC0SymbolUtil
    : Lean.TSyntax `term → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `c0_symbol)
| `(c0_symbol% $x) => return x
| `(($x)) => unexpandC0SymbolUtil x
| _ => throw ()

@[inline]
partial def unexpandC0TypedSymbolUtil
    : Lean.TSyntax `term
    → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `c0_symbol × Lean.TSyntax `c0_type)
| `(c0_tsymbol% $x:c0_symbol :ₛ $τ) => return ⟨x, τ⟩
| `(($x)) => unexpandC0TypedSymbolUtil x
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
| `($_ $s) => do `(c0_type% struct $(← unexpandC0SymbolUtil s))
| _ => throw ()

@[app_unexpander Typ.mem]
def unexpandTypMem : Lean.PrettyPrinter.Unexpander
| `($_ (c0_type% $τ)) => `((c0_type% $τ))
| _ => throw ()

@[app_unexpander Typ.Typed.mk]
def unexpandTyped : Lean.PrettyPrinter.Unexpander
| `($_ (c0_type% $τ) >>c0_expr| $e <<) =>
    `(>>c0_texpr| $e:c0_expr : $τ:c0_type <<)
| `($_ (c0_type% $τ) >>c0_lvalue| $l <<) =>
    `(>>c0_tlvalue| $l:c0_lvalue : $τ:c0_type <<)
| `($_ (c0_type% $τ) $x) => do
    `(c0_tsymbol% $(← unexpandC0SymbolUtil x):c0_symbol :ₛ $τ)
| _ => throw ()

/-
  Expr Unexpanders
-/
@[app_unexpander Expr.num]
def unexpandExprNum : Lean.PrettyPrinter.Unexpander
| `($_ $x:num) => `(>>c0_expr| $x:num <<)
| _ => throw ()

@[app_unexpander Expr.char]
def unexpandExprChar : Lean.PrettyPrinter.Unexpander
| `($_ $c:char) => `(>>c0_expr| $c:char <<)
| _ => throw ()

@[app_unexpander Expr.str]
def unexpandExprStr : Lean.PrettyPrinter.Unexpander
| `($_ $s:str) => `(>>c0_expr| $s:str <<)
| _ => throw ()

@[app_unexpander Expr.var]
def unexpandExprVar : Lean.PrettyPrinter.Unexpander
| `($_ $x) => do `(>>c0_expr| $(← unexpandC0SymbolUtil x):c0_symbol <<)
| _ => throw ()

@[app_unexpander Expr.true]
def unexpandExprTrue : Lean.PrettyPrinter.Unexpander
| `($_) => `(>>c0_expr| true <<)

@[app_unexpander Expr.false]
def unexpandFalse : Lean.PrettyPrinter.Unexpander
| `($_) => `(>>c0_expr| false <<)

@[app_unexpander Expr.null]
def unexpandExprNull : Lean.PrettyPrinter.Unexpander
| `($_) => `(>>c0_expr| null <<)

@[app_unexpander Expr.unop_int]
def unexpandExprUnopInt : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $e <<) =>
  match op.raw.getId with
  | `Tst.UnOp.Int.not => `(>>c0_expr| ~ $e <<)
  | `Tst.UnOp.Int.neg => `(>>c0_expr| - $e <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.unop_bool]
def unexpandExprUnopBool : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $e <<) =>
  match op.raw.getId with
  | `Tst.UnOp.Bool.neg => `(>>c0_expr| ! $e <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.binop_int]
def unexpandExprBinopInt : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $l << >>c0_texpr| $r <<) =>
  match op.raw.getId with
  | `Tst.BinOp.Int.plus   => `(>>c0_expr| ($l:c0_texpr + $r) <<)
  | `Tst.BinOp.Int.minus  => `(>>c0_expr| ($l:c0_texpr - $r) <<)
  | `Tst.BinOp.Int.times  => `(>>c0_expr| ($l:c0_texpr * $r) <<)
  | `Tst.BinOp.Int.div    => `(>>c0_expr| ($l:c0_texpr / $r) <<)
  | `Tst.BinOp.Int.mod    => `(>>c0_expr| ($l:c0_texpr % $r) <<)
  | `Tst.BinOp.Int.and    => `(>>c0_expr| ($l:c0_texpr & $r) <<)
  | `Tst.BinOp.Int.or     => `(>>c0_expr| ($l:c0_texpr | $r) <<)
  | `Tst.BinOp.Int.xor    => `(>>c0_expr| ($l:c0_texpr ^ $r) <<)
  | `Tst.BinOp.Int.lsh    => `(>>c0_expr| ($l:c0_texpr << $r) <<)
  | `Tst.BinOp.Int.rsh    => `(>>c0_expr| ($l:c0_texpr >> $r) <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.binop_bool]
def unexpandExprBinopBool : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $l << >>c0_texpr| $r <<) =>
  match op.raw.getId with
  | `Tst.BinOp.Bool.and => `(>>c0_expr| ($l:c0_texpr && $r) <<)
  | `Tst.BinOp.Bool.or  => `(>>c0_expr| ($l:c0_texpr || $r) <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.binop_eq]
def unexpandExprBinopEq : Lean.PrettyPrinter.Unexpander
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
def unexpandExprBinopRelChar : Lean.PrettyPrinter.Unexpander
| `($_ $op >>c0_texpr| $l << >>c0_texpr| $r <<) =>
  match op.raw.getId with
  | `Comparator.less          => `(>>c0_expr| ($l:c0_texpr < $r) <<)
  | `Comparator.less_equal    => `(>>c0_expr| ($l:c0_texpr <= $r) <<)
  | `Comparator.greater       => `(>>c0_expr| ($l:c0_texpr > $r) <<)
  | `Comparator.greater_equal => `(>>c0_expr| ($l:c0_texpr >= $r) <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Expr.ternop]
def unexpandExprTernop : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $c << >>c0_texpr| $t << >>c0_texpr| $f <<) =>
    `(>>c0_expr| ($c:c0_texpr ? $t : $f) <<)
| _ => throw ()

@[app_unexpander Expr.app]
def unexpandExprApp : Lean.PrettyPrinter.Unexpander
| `($_ $f [ ]) => do `(>>c0_expr| $(← unexpandC0SymbolUtil f):c0_symbol(-) <<)
-- | `($_ $f $args) => unexpandC0SymbolUtil (fun f => `(>>c0_expr| $f:c0_symbol(-) <<)) f
| _ => throw ()
-- todo function app

@[app_unexpander Expr.alloc]
def unexpandExprAlloc : Lean.PrettyPrinter.Unexpander
| `($_ (c0_type% $τ)) => `(>>c0_expr| alloc($τ) <<)
| _ => throw ()

@[app_unexpander Expr.alloc_array]
def unexpandExprAllocArray : Lean.PrettyPrinter.Unexpander
| `($_ (c0_type% $τ) >>c0_texpr| $e <<) =>
    `(>>c0_expr| alloc_array($τ, $e) <<)
| _ => throw ()

@[app_unexpander Expr.dot]
def unexpandExprDot : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e << $f) => do
    `(>>c0_expr| $e:c0_texpr. $(← unexpandC0SymbolUtil f)<<)
| _ => throw ()

@[app_unexpander Expr.deref]
def unexpandExprDeref : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_expr| *$e <<)
| _ => throw ()

@[app_unexpander Expr.index]
def unexpandExprIndex : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $a << >>c0_texpr| $i <<) =>
    `(>>c0_expr| $a:c0_texpr[$i] <<)
| _ => throw ()

@[app_unexpander Expr.result]
def unexpandExprResult : Lean.PrettyPrinter.Unexpander
| `($_) => `(>>c0_expr| \result <<)

@[app_unexpander Expr.length]
def unexpandExprLength : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_expr| *$e <<)
| _ => throw ()

/-
  LValue Unexpanders
-/
@[app_unexpander LValue.var]
def unexpandLValueVar : Lean.PrettyPrinter.Unexpander
| `($_ $x) => do `(>>c0_lvalue| $(← unexpandC0SymbolUtil x):c0_symbol <<)
| _ => throw ()

@[app_unexpander LValue.dot]
def unexpandLValueDot : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_tlvalue| $l << $f) => do
    `(>>c0_lvalue| $l:c0_tlvalue. $(← unexpandC0SymbolUtil f)<<)
| _ => throw ()

@[app_unexpander LValue.deref]
def unexpandLValueDeref : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_tlvalue| $l <<) => `(>>c0_lvalue| *$l <<)
| _ => throw ()

@[app_unexpander LValue.index]
def unexpandLValueIndex : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_tlvalue| $a << >>c0_texpr| $i <<) =>
    `(>>c0_lvalue| $a:c0_tlvalue[$i] <<)
| _ => throw ()

/-
  Annotation Unexpanders
-/
@[app_unexpander Anno.requires]
def unexpandAnnoRequires : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_anno| //@requires $e <<)
| _ => throw ()

@[app_unexpander Anno.ensures]
def unexpandAnnoEnsures : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_anno| //@ensures $e <<)
| _ => throw ()

@[app_unexpander Anno.loop_invar]
def unexpandAnnoLoopInvar : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_anno| //@loop_invariant $e <<)
| _ => throw ()

@[app_unexpander Anno.assert]
def unexpandAnnoAssert : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_anno| //@assert $e <<)
| _ => throw ()

/-
  Statement Unexpanders
-/
@[inline]
def unexpandStmts
    (stmtTermList : Lean.Syntax.TSepArray `term s)
    : Lean.PrettyPrinter.UnexpandM (Lean.Syntax.TSepArray `c0_stmt ";") := do
  let stmtArray ← stmtTermList.getElems.mapM (
      fun | `(>>c0_stmt| $s <<) => return s
          | _ => throw ()
    )
  return Lean.Syntax.TSepArray.ofElems stmtArray

@[app_unexpander Stmt.decl]
def unexpandStmtDecl : Lean.PrettyPrinter.Unexpander
| `($_ $x [ $stmtTermList,* ]) => do
  let (x, τ) ← unexpandC0TypedSymbolUtil x
  let sepStmtArray ← unexpandStmts stmtTermList
  `(>>c0_stmt| $τ:c0_type $x { $sepStmtArray;* } <<)
| _ => throw ()

@[app_unexpander Stmt.decl_init]
def unexpandStmtDeclInit : Lean.PrettyPrinter.Unexpander
| `($_ $x >>c0_texpr| $e << [ $stmtTermList,* ]) => do
  let (x, τ) ← unexpandC0TypedSymbolUtil x
  let sepStmtArray ← unexpandStmts stmtTermList
  `(>>c0_stmt| $τ:c0_type $x = $e { $sepStmtArray;* } <<)
| _ => throw ()

@[app_unexpander Stmt.assign_var]
def unexpandStmtAssignVar : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_tlvalue| $x:c0_symbol : $τ:c0_type << >>c0_texpr| $e <<) =>
    `(>>c0_stmt| $x:c0_symbol : $τ:c0_type = $e <<)
| _ => throw ()

@[app_unexpander Stmt.assign]
def unexpandStmtAssign : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_tlvalue| $l << >>c0_texpr| $e <<) =>
    `(>>c0_stmt| $l:c0_tlvalue = $e <<)
| _ => throw ()

@[app_unexpander Stmt.asnop]
def unexpandStmtAsnop : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_tlvalue| $l << $op >>c0_texpr| $e <<) =>
  match op.raw.getId with
  | `Tst.BinOp.Int.plus   => `(>>c0_stmt| $l:c0_tlvalue += $e <<)
  | `Tst.BinOp.Int.minus  => `(>>c0_stmt| $l:c0_tlvalue -= $e <<)
  | `Tst.BinOp.Int.times  => `(>>c0_stmt| $l:c0_tlvalue *= $e <<)
  | `Tst.BinOp.Int.div    => `(>>c0_stmt| $l:c0_tlvalue /= $e <<)
  | `Tst.BinOp.Int.mod    => `(>>c0_stmt| $l:c0_tlvalue %= $e <<)
  | `Tst.BinOp.Int.and    => `(>>c0_stmt| $l:c0_tlvalue &= $e <<)
  | `Tst.BinOp.Int.or     => `(>>c0_stmt| $l:c0_tlvalue |= $e <<)
  | `Tst.BinOp.Int.xor    => `(>>c0_stmt| $l:c0_tlvalue ^= $e <<)
  | `Tst.BinOp.Int.lsh    => `(>>c0_stmt| $l:c0_tlvalue <<= $e <<)
  | `Tst.BinOp.Int.rsh    => throw ()
    -- let test : Lean.TSyntax `c0_binop_int := (Lean.quote ">>")
    -- `(>>c0_stmt| $l:c0_tlvalue $test:c0_binop_int= $e <<)
  | _ => throw ()
| _ => throw ()

@[app_unexpander Stmt.expr]
def unexpandStmtExpr : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_stmt| $e:c0_texpr <<)
| _ => throw ()

@[app_unexpander Stmt.ite]
def unexpandStmtIte : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e << [ $t,* ] [ $f,* ]) => do
  let sepThenArray ← unexpandStmts t
  let sepElseArray ← unexpandStmts f
  `(>>c0_stmt| if($e:c0_texpr) { $sepThenArray;* } else { $sepElseArray;* } <<)
| _ => throw ()

@[app_unexpander Stmt.while]
def unexpandStmtWhile : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e << [ $b,* ]) => do
  let sepBodyArray ← unexpandStmts b
  `(>>c0_stmt| while($e:c0_texpr) { $sepBodyArray;* } <<)
| _ => throw ()

@[app_unexpander Stmt.return_void]
def unexpandStmtReturnVoid : Lean.PrettyPrinter.Unexpander
| `($_) => `(>>c0_stmt| return <<)

@[app_unexpander Stmt.return_tau]
def unexpandStmtReturnTau : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_stmt| return $e <<)
| _ => throw ()

@[app_unexpander Stmt.assert]
def unexpandStmtAssert : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_stmt| assert($e) <<)
| _ => throw ()

@[app_unexpander Stmt.error]
def unexpandStmtError : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_texpr| $e <<) => `(>>c0_stmt| error($e) <<)
| _ => throw ()

@[app_unexpander Stmt.anno]
def unexpandStmtAnno : Lean.PrettyPrinter.Unexpander
| `($_ >>c0_anno| $a <<) => `(>>c0_stmt| $a:c0_anno <<)
| _ => throw ()

#check >>c0_texpr| (x₅ : int + 5 : int) : int <<
#check >>c0_expr| (5 : int) >= (5 : int) <<
#check >>c0_expr| f₀(x₁ : int) <<

#check Typ.Typed.mk (c0_type% int) (c0_symbol% x₁)
#check Expr.app ⟨"f", 0⟩ .nil

#check Pst.Stmt.decl (c0_tsymbol% x₁ :ₛ int) .nil
#check Pst.Stmt.decl_init (c0_tsymbol% x₁ :ₛ int) (>>c0_texpr| (100 : int + ((5 : int) * 10 : int) : int) : int <<) .nil
#check Pst.Stmt.decl_init (c0_tsymbol% x₁ :ₛ int) (>>c0_texpr| (100 : int + ((5 : int) * 10 : int) : int) : int <<)
      [Pst.Stmt.anno (>>c0_anno| //@assert (x₁ : int == 150 : int) : bool <<),
        Pst.Stmt.return_tau (>>c0_texpr| x₁ : int <<)]
#check Pst.Stmt.decl_init (c0_tsymbol% x₁ :ₛ int) (>>c0_texpr| (100 : int + ((5 : int) * 10 : int) : int) : int <<)
      [ Pst.Stmt.decl_init (c0_tsymbol% x₁ :ₛ int) (>>c0_texpr| (100 : int + ((5 : int) * 10 : int) : int) : int <<) [ ]
      , Pst.Stmt.decl_init (c0_tsymbol% x₁ :ₛ int) (>>c0_texpr| (100 : int + ((5 : int) * 10 : int) : int) : int <<) [ ]
      ]

#check Pst.Expr.binop_int Tst.BinOp.Int.plus (Typ.Typed.mk (Typ.prim Typ.Primitive.int) (Pst.Expr.num 100))
          (Typ.Typed.mk (Typ.prim Typ.Primitive.int) (Pst.Expr.num 50))
