import Std

import C0deine.Utils.Context
import C0deine.Parser.Cst
import C0deine.Parser.ParserT
import C0deine.AuxDefs

namespace C0deine.Parser


abbrev C0Parser (s) := ParserT Context s

namespace C0Parser

open ParserT Cst

nonrec def withBacktracking (p : C0Parser s α) := withBacktracking p 
nonrec def withBacktrackingUntil (p : C0Parser s α) (q : α → C0Parser s β)
  := withBacktrackingUntil p q

def intmin : Int := -2147483648

def num : C0Parser s Int :=
  first
  [ dec
  , hex
  , (do char '0'; notFollowedBy (do let _ ← charMatching (·.isHexDigit)); return 0)
  , (do wholeString "-2147483648"; return intmin)
  ]
where
  dec : C0Parser s Int := do
    let digs ←
      foldl
        (do return (← charMatching (fun c => '1' ≤ c && c ≤ '9')).toString)
        (fun acc => do
          let c ← charMatching (fun c => '0' ≤ c && c ≤ '9')
          return String.push acc c)
    return Nat.ofDigits? 10 digs |>.get!
  hex : C0Parser s Int := do
    withBacktracking (do
      char '0'
      (char 'x' <|> char 'X')
    )
    let digs ←
      foldl (return "") (fun s => do
        let c ← charMatching (fun c => '0' ≤ c && c ≤ '9' || 'a' ≤ c && c ≤ 'f' || 'A' ≤ c && c ≤ 'F')
        return s.push c)
    if digs.length = 0 then
      throwUnexpected -- fun () => "expected [0-9a-fA-F]"
    let nat := Nat.ofDigits? 16 digs |>.get!
    return nat


def lineComment : C0Parser s Unit := do
  wholeString "//"
  dropMany (do let _ ← charMatching (· ≠ '\n'))

partial def blockComment : C0Parser s Unit := do
  wholeString "/*"
  dropMany (
        (do let _ ← charMatching (¬ · ∈ ['/', '*']))
    <|> (withBacktracking do char '*'; notFollowedBy (char '/'))
    <|> (withBacktracking do char '/'; notFollowedBy (char '*'))
    <|> blockComment)
  wholeString "*/"

def ws : C0Parser s Unit :=
  withContext "ws" <|
  dropMany (
    (withBacktracking do
      let a ← any; guard ((a : Char) ∈ [' ', '\n', '\t', '\r', '\u0011', '\u0012']))
    <|> lineComment
    <|> blockComment)

@[inline] def keyword (kw : String) : C0Parser s Unit :=
  atomically (name := s!"\"{kw}\"") do
  /- keywords should not be followed by alphanums-/
  wholeString kw
  notFollowedBy (do let _ ← charMatching (fun c => c.isAlphanum || c = '_'))

def kw_struct       : C0Parser s Unit := keyword "struct"
def kw_typedef      : C0Parser s Unit := keyword "typedef"
def kw_if           : C0Parser s Unit := keyword "if"
def kw_else         : C0Parser s Unit := keyword "else"
def kw_while        : C0Parser s Unit := keyword "while"
def kw_for          : C0Parser s Unit := keyword "for"
def kw_continue     : C0Parser s Unit := keyword "continue"
def kw_break        : C0Parser s Unit := keyword "break"
def kw_return       : C0Parser s Unit := keyword "return"
def kw_assert       : C0Parser s Unit := keyword "assert"
def kw_true         : C0Parser s Unit := keyword "true"
def kw_false        : C0Parser s Unit := keyword "false"
def kw_NULL         : C0Parser s Unit := keyword "NULL"
def kw_alloc        : C0Parser s Unit := keyword "alloc"
def kw_alloc_array  : C0Parser s Unit := keyword "alloc_array"
def kw_int          : C0Parser s Unit := keyword "int"
def kw_bool         : C0Parser s Unit := keyword "bool"
def kw_void         : C0Parser s Unit := keyword "void"
def kw_char         : C0Parser s Unit := keyword "char"
def kw_string       : C0Parser s Unit := keyword "string"

def anyKeyword : C0Parser s Unit :=
  first [
    kw_struct
  , kw_typedef
  , kw_if
  , kw_else
  , kw_while
  , kw_for
  , kw_continue
  , kw_break
  , kw_return
  , kw_assert
  , kw_true
  , kw_false
  , kw_NULL
  , kw_alloc
  , kw_alloc_array
  , kw_int
  , kw_bool
  , kw_void
  , kw_char
  , kw_string
  ]

variable (tydefs : Std.RBSet Symbol Ord.compare)

def rawIdent : C0Parser s Ident := do
  notFollowedBy anyKeyword
  let c ← charMatching (fun c => c.isAlpha || c = '_')
  let str ← foldl (return c.toString) (fun s => do
    let c ← charMatching (fun c => c.isAlphanum || c = '_')
    return s.push c)
  return ← liftM <| Symbol.symbol str

def typeIdent : C0Parser s Ident :=
  withContext "<type-ident>" <|
  withBacktracking do
  let id ← rawIdent
  if tydefs.contains id then
    return id
  else
    throwUnexpected

def ident : C0Parser s Ident :=
  withContext "<ident>" <|
  withBacktracking do
  let id ← rawIdent
  if tydefs.contains id then
    throwUnexpected
  else
    return id


mutual
def simpleTyp : C0Parser s Typ :=
  first [
    (do kw_int ; return Typ.int)
  , (do kw_bool; return Typ.bool)
  , (do kw_void; return Typ.void)
  , (do let name ← typeIdent tydefs; return Typ.tydef name)
  , (do kw_struct; ws; let name ← rawIdent; return Typ.struct name)
  ]

def typ : C0Parser s Typ :=
  withContext "<type>" do
  -- parse a simple type
  let t ← simpleTyp
  -- parse as many * and [] as we can
  foldl (return t)
    (fun t =>
      (do withBacktracking (do ws; char '*'); return Typ.ptr t)
      <|> (do withBacktracking (do ws; char '['); ws; char ']'; return Typ.arr t) )
end

def unop.int : C0Parser s UnOp.Int :=
  first [
    (do char '-'; notFollowedBy (char '-'); notFollowedBy (char '>'); return .neg)
  , (do char '~'; return .not)
  ]

def unop.bool : C0Parser s UnOp.Bool :=
  (do char '!'; return .not)

def unop : C0Parser s UnOp :=
  first [
    (do let op ← unop.int; return .int op)
  , (do let op ← unop.bool; return .bool op)
  ]

def binop.int.prec_11 : C0Parser s BinOp.Int :=
  first [
    (do char '*'; return .times)
  , (do char '/'; return .div)
  , (do char '%'; return .mod)
  ]

def binop.int.prec_10 : C0Parser s BinOp.Int :=
  first [
    (do char '+'; return .plus)
  , (withBacktracking do char '-'; notFollowedBy (char '-'); return .minus)
  ]

def binop.int.prec_9 : C0Parser s BinOp.Int :=
  first [
    (do wholeString "<<"; return .lsh)
  , (do wholeString ">>"; return .rsh)
  ]

def binop.cmp.prec_8 : C0Parser s BinOp.Cmp :=
  first [
    (do char '<'; return .lt)
  , (do wholeString "<="; return .le)
  , (do char '>'; return .gt)
  , (do wholeString ">="; return .ge)
  ]

def binop.cmp.prec_7 : C0Parser s BinOp.Cmp :=
  first [
    (do wholeString "=="; return .eq)
  , (do wholeString "!="; return .ne)
  ]

def binop.int.prec_6 : C0Parser s BinOp.Int :=
  (do char '&'; return .and)

def binop.int.prec_5 : C0Parser s BinOp.Int :=
  (do char '^'; return .xor)

def binop.int.prec_4 : C0Parser s BinOp.Int :=
  (do char '|'; return .or)

def binop.bool.prec_3 : C0Parser s BinOp.Bool :=
  (do wholeString "&&"; return .and)

def binop.bool.prec_2 : C0Parser s BinOp.Bool :=
  (do wholeString "||"; return .or)

def binop.int : C0Parser s BinOp.Int :=
  first [
    binop.int.prec_11 , binop.int.prec_10 , binop.int.prec_9
  , binop.int.prec_6  , binop.int.prec_5  , binop.int.prec_4
  ]

def asnop : C0Parser s AsnOp :=
    (do char '='; return .eq)
<|> (do let op ← binop.int; char '='; return .aseq op)

def postop : C0Parser s PostOp :=
    (do wholeString "++"; return .incr)
<|> (do wholeString "--"; return .decr)

mutual
partial def expr.prec_13 : C0Parser s Expr :=
  foldl (left <* ws) (fun lhs => right lhs <* ws)
where
  left : C0Parser s Expr :=
    first [
      (do let v ← num; return .num v)
    , (do kw_true; return .«true»)
    , (do kw_false; return .«false»)
    , (do kw_NULL; return .null)
    , (do kw_alloc; ws; char '('; ws
          let ty ← typ tydefs
          ws; char ')'
          return .alloc ty)
    , (do kw_alloc_array; ws; char '('; ws
          let ty ← typ tydefs
          ws; char ','; ws
          let e ← expr
          ws; char ')'
          return .alloc_array ty e)
    , (do let name ← ident tydefs
          (do ws; char '('; ws
              let args ← foldl
                (do let e ← expr; return #[e])
                (fun acc => do ws; char ','; ws; return acc.push (← expr))
              char ')'
              return .app name args.toList)
          <|>
          (return .var name))
    , (do char '('; let e ← expr; char ')'; return e)
    ]
  right (lhs) := do
    first [
      (do char '.'; ws; let f ← ident tydefs
          return (.dot lhs f))
    , (do wholeString "->"; ws; let f ← ident tydefs
          return (.arrow lhs f))
    , (do char '['; ws; let e ← expr
          return (.index lhs e))
    ]


partial def expr.prec_12 : C0Parser s Expr :=
  first [
    (do let op ← unop; ws; return .unop op (← expr.prec_12))
  , (do char '*'; ws; return .deref (← expr.prec_12))
  , expr.prec_13
  ]

partial def expr.prec_11 : C0Parser s Expr :=
  foldl (expr.prec_12 <* ws) (fun lhs => do
    let op ← binop.int.prec_11; ws; let rhs ← expr.prec_12; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_10 : C0Parser s Expr :=
  foldl (expr.prec_11 <* ws) (fun lhs => do
    let op ← binop.int.prec_10; ws; let rhs ← expr.prec_11; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_9 : C0Parser s Expr :=
  foldl (expr.prec_10 <* ws) (fun lhs => do
    let op ← binop.int.prec_9; ws; let rhs ← expr.prec_10; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_8 : C0Parser s Expr :=
  foldl (expr.prec_9 <* ws) (fun lhs => do
    let op ← binop.cmp.prec_8; ws; let rhs ← expr.prec_9; ws
    return (.binop (.cmp op) lhs rhs))

partial def expr.prec_7 : C0Parser s Expr :=
  foldl (expr.prec_8 <* ws) (fun lhs => do
    let op ← binop.cmp.prec_7; ws; let rhs ← expr.prec_8; ws
    return (.binop (.cmp op) lhs rhs))

partial def expr.prec_6 : C0Parser s Expr :=
  foldl (expr.prec_7 <* ws) (fun lhs => do
    let op ← binop.int.prec_6; ws; let rhs ← expr.prec_7; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_5 : C0Parser s Expr :=
  foldl (expr.prec_6 <* ws) (fun lhs => do
    let op ← binop.int.prec_5; ws; let rhs ← expr.prec_6; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_4 : C0Parser s Expr :=
  foldl (expr.prec_5 <* ws) (fun lhs => do
    let op ← binop.int.prec_4; ws; let rhs ← expr.prec_5; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_3 : C0Parser s Expr :=
  foldl (expr.prec_4 <* ws) (fun lhs => do
    let op ← binop.bool.prec_3; ws; let rhs ← expr.prec_4; ws
    return (.binop (.bool op) lhs rhs))

partial def expr.prec_2 : C0Parser s Expr :=
  foldl (expr.prec_3 <* ws) (fun lhs => do
    let op ← binop.bool.prec_2; ws; let rhs ← expr.prec_3; ws
    return (.binop (.bool op) lhs rhs))

partial def expr.prec_1 : C0Parser s Expr := do
  let lhs ← expr.prec_2
  -- Note whitespace already has been consumed
  (do char '?'; ws
      let tt ← expr.prec_1; ws
      char ':'; ws; let ff ← expr.prec_1;
      return .ternop lhs tt ff)
  <|> (do return lhs)

partial def expr : C0Parser s Expr := expr.prec_1
end

partial def lvalue : C0Parser s LValue :=
  withContext "<lvalue>" <|
  foldl
    (do let name ← ident tydefs; return .var name)
    (fun lv =>
      withBacktrackingUntil ws
      (fun () => first [
        (do
        char '.'; ws
        let field ← ident tydefs
        return (.dot lv field))
      , (do
        wholeString "->"; ws
        let field ← ident tydefs
        return (.arrow lv field))
      , (do
        char '*'; ws
        return (.deref lv))
      , (do
        char '['; ws; let index ← expr tydefs; char ']'
        return (.index lv index))
      ])
    )


mutual
partial def control : C0Parser s Control :=
  first [
    (do kw_if; ws; char '('; ws; let cond ← expr tydefs; ws; char ')'; ws
        let tt ← stmt
        let ff ← option (do withBacktracking (do ws; kw_else); stmt)
        return Control.ite cond tt (ff.getD (.block [])))
  , (do kw_while; ws; char '('; ws; let cond ← expr tydefs; ws; char ')'; ws
        let body ← stmt
        return Control.«while» cond body)
  , (do kw_for; ws; char '('; ws
        let init ← simp; ws; char ';'; ws
        let cond ← expr tydefs; ws; char ';'; ws
        let step ← option simp; ws
        char ')'; ws
        let body ← stmt
        return Control.«for» init cond step body)
  , (do kw_return; ws; let e ← option (expr tydefs); ws; char ';'
        return Control.«return» e)
  , (do kw_assert; ws; let e ← expr tydefs; ws; char ';'
        return Control.assert e)
  ]

partial def simp : C0Parser s Simp :=
  first [
    (do
      let type ← typ tydefs; ws
      let name ← ident tydefs; ws;
      let init ← option (do char '='; ws; expr tydefs)
      return .decl type name init)
  , (do
      let lv ← lvalue tydefs; ws
      -- either an asnop, or a postop, OR an expression
      -- with `lv` on the LHS
      (do let op ← asnop; ws; let v ← expr tydefs; return .assn lv op v)
      <|>
      (do let op ← postop; return .post lv op)
      -- TODO: allow lvalues to reduce to LHS of expression
      --<|>
      --(expr.prec_13.right)
      )
  , (do let e ← expr tydefs; return .exp e)
  ]

partial def block : C0Parser s Stmt := do
  char '{'; ws
  let body ← sepBy ws stmt
  ws; char '}'
  return .block body.toList

partial def stmt : C0Parser s Stmt :=
  first [
    (do let s ← simp; ws; char ';'; return .simp s)
  , (do return .ctrl (←control))
  , block
  ]

end

def field : C0Parser s Field :=
  withContext "<struct-field>" do
  let type ← typ tydefs
  ws
  let name ← ident tydefs
  char ';'
  return ⟨type, name⟩

def sdef : C0Parser s SDef :=
  withContext "<struct-def>" do
  let name ← withBacktracking do
    kw_struct; ws
    let name ← ident tydefs; ws
    char '{'
    pure name
  ws
  let fields ← sepBy ws (field tydefs)
  ws; char '}'; char ';'
  return ⟨name, fields.toList⟩

def sdecl : C0Parser s SDecl :=
  withContext "<struct-decl>" <|
  withBacktracking do
  kw_struct; ws
  let name ← ident tydefs; ws
  char ';'
  return ⟨name⟩

def tydef : C0Parser s TyDef :=
  withContext "<type-def>" do
  kw_typedef; ws
  let type ← typ tydefs; ws
  let name ← ident tydefs; ws
  char ';'
  return ⟨type, name⟩

def param : C0Parser s Param := do
  let type ← typ tydefs; ws
  let name ← ident tydefs
  return ⟨type, name⟩

private def signature : C0Parser s FDecl :=
  withContext "<func-sig>" do
  let type ← typ tydefs; ws
  let name ← ident tydefs; ws
  char '('; ws
  let params ← sepBy (do ws; char ','; ws) (param tydefs)
  ws; char ')'
  return ⟨type, name, params.toList⟩

def fdecl (sig : FDecl) : C0Parser s FDecl :=
  withContext "<func-decl>" <|
  withBacktracking do
  ws; char ';'
  return sig

def fdef (sig : FDecl) : C0Parser s FDef :=
  withContext "<func-def>" do
  ws
  let body ← block tydefs
  return {sig with body}

def gdecl : C0Parser s GDecl :=
  first
  [do return .tydef (← tydef tydefs)
  ,do return .sdecl (← sdecl tydefs)
  ,do return .sdef  (← sdef  tydefs)
  ,do let sig ← signature tydefs
      (return .fdecl (← fdecl sig)) 
      <|> (return .fdef (← fdef tydefs sig))
  ]

partial def prog : C0Parser s Prog := do
  ws
  let gdecls ← aux (Std.RBSet.empty) #[]
  return gdecls.toList
where aux tydefs acc :=
  (do eof; return acc)
  <|> (do
    let g ← gdecl tydefs
    ws
    let tydefs := match g with | .tydef ⟨_, i⟩ => tydefs.insert i | _ => tydefs
    aux tydefs (acc.push g))
