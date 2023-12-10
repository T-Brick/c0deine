import Std
import Numbers

import C0deine.Context.Context
import C0deine.Parser.Cst
import C0deine.Parser.ParserT
import C0deine.AuxDefs

namespace C0deine.Parser


abbrev C0Parser (s) := ParserT Context s

namespace C0Parser

open ParserT Cst Numbers

@[inline] nonrec def withBacktracking (p : C0Parser s α) := withBacktracking p
@[inline] nonrec def withBacktrackingUntil (p : C0Parser s α) (q : α → C0Parser s β)
  := withBacktrackingUntil p q

def num : C0Parser s Int32 :=
  first
  [ dec
  , hex
  , (do char '0'; notFollowedBy (do let _ ← charMatching (·.isHexDigit)); return .ofNat 0)
  ]
where
  dec : C0Parser s Int32 := do
    let digs ←
      foldl
        (do return (← charMatching (fun c => '1' ≤ c && c ≤ '9')).toString)
        (fun acc => do
          let c ← charMatching (fun c => '0' ≤ c && c ≤ '9')
          return String.push acc c)
    let nat := Nat.ofDigits? 10 digs |>.get!
    if nat = 2^31 then
      return Signed.MIN_VALUE
    else if h : nat < 2^31 then
      return .ofNat nat
    else
      throwExpected (fun () => [s!"dec literal ≤ {2^31}"])
  hex : C0Parser s Int32 := do
    withBacktracking (do
      char '0'
      (char 'x' <|> char 'X')
    )
    let digs ←
      foldl (do return (← hexDig).toString) (fun (s : String) => do
        let c ← hexDig
        return s.push c)
    let nat := Nat.ofDigits? 16 digs |>.get!
    if h : nat < UInt32.size then
      return .ofNat nat
    else
      throwExpected (fun () => [s!"hex literal ≤ {2^32-1 |>.toDigits (base := 16) |> String.mk}"])
  hexDig := charMatching (fun c => '0' ≤ c && c ≤ '9' || 'a' ≤ c && c ≤ 'f' || 'A' ≤ c && c ≤ 'F')

def esc_seq : C0Parser s Char := do
  char '\\'
  (do char 'n'; return '\n')
  <|> (do char 't'; return '\t')
  <|> (do char 'v'; return Char.ofNat 0x0B)
  <|> (do char 'b'; return Char.ofNat 0x08)
  <|> (do char 'r'; return '\r')
  <|> (do char 'f'; return Char.ofNat 0x0C)
  <|> (do char 'a'; return Char.ofNat 0x07)
  <|> (do char '\\'; return '\\')
  <|> (do char '\''; return '\'')
  <|> (do char '"'; return '"')

def chrlit : C0Parser s Char := do
  char '\''
  let c : Char ←
    (do char '"'; return '"')
    <|> (withBacktracking do return ←esc_seq)
    <|> (do char '\\'; char '0'; return Char.ofNat 0x00)
    <|> (do return ←charMatching (fun c => 32 ≤ c.val && c.val < 127 && c ≠ '\'' )) -- nchar
  char '\''
  return c

partial def strlit : C0Parser s String := do
  char '"'
  return String.mk (← aux)
where aux : C0Parser s (List Char) := do
  (do char '"'; return [])
  <|> (do let c ← esc_seq
          let cs ← aux
          return c :: cs)
  <|> (do let c ← charMatching (fun | '"'  => false
                                    | '\n' => false
                                    | c    => 32 ≤ c.val && c.val < 127)
          let cs ← aux
          return c :: cs)

partial def liblit : C0Parser s String := do
  char '<'
  return String.mk (← aux)
where aux : C0Parser s (List Char) := do
  (do char '>'; return [])
  <|> (do let c ← charMatching (fun | '>'  => false
                                    | '\n' => false
                                    | c    => 32 ≤ c.val && c.val < 127)
          let cs ← aux
          return c :: cs)
  <|> (do let c ← esc_seq
          let cs ← aux
          return c :: cs)

def lineComment : C0Parser s Unit :=
  withBacktracking do
  wholeString "//"
  let c ← charMatching (· ≠ '@')
  if c = '\n' then return ()
  dropMany (do let _ ← charMatching (· ≠ '\n'))

partial def blockComment : C0Parser s Unit :=
  withBacktracking do
  wholeString "/*"
  let _ ← charMatching (· ≠ '@')
  dropMany (
        (do let _ ← charMatching (¬ · ∈ ['/', '*']))
    <|> (withBacktracking do char '*'; notFollowedBy (char '/'))
    <|> (withBacktracking do char '/'; notFollowedBy (char '*'))
    <|> blockComment)
  wholeString "*/"

def ws_no_newline : C0Parser s Unit :=
  withContext "ws_no_newline" <|
  dropMany (
    (first [  char ' ', char '\t', char '\r'
            , char (11 : UInt8), char (12 : UInt8)])
    <|> lineComment
    <|> blockComment)

def ws : C0Parser s Unit :=
  withContext "ws" <|
  dropMany (
    (first [  char ' ', char '\n', char '\t', char '\r'
            , char (11 : UInt8), char (12 : UInt8)])
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
def kw_error        : C0Parser s Unit := keyword "error"
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
def kw_result       : C0Parser s Unit := keyword "\\result"
def kw_length       : C0Parser s Unit := keyword "\\length"
def kw_requires     : C0Parser s Unit := keyword "requires"
def kw_ensures      : C0Parser s Unit := keyword "ensures"
def kw_loop_invar   : C0Parser s Unit := keyword "loop_invariant"
def kw_use          : C0Parser s Unit := keyword "use"

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
  , kw_error
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
  , kw_result
  , kw_length
  , kw_requires
  , kw_ensures
  , kw_loop_invar
  , kw_use
  ]

variable (tydefs : Std.RBSet Symbol Ord.compare)

def rawIdent : C0Parser s Ident :=
  atomically do
  notFollowedBy anyKeyword
  let str ←
    foldl
      (do let c ← charMatching (fun c => c.isAlpha || c = '_')
          return c.toString)
      (fun s => do
        let c ← charMatching (fun c => c.isAlphanum || c = '_')
        return s.push c)
  return ← liftM <| Symbol.symbol str

def typeIdent : C0Parser s Ident :=
  atomically (name := "<type-ident>") do
  let id ← rawIdent
  if tydefs.contains id then
    return id
  else
    throwUnexpected

def ident : C0Parser s Ident :=
  atomically (name := "<ident>") do
  let id ← rawIdent
  if tydefs.contains id then
    throwUnexpected
  else
    return id


mutual
def simpleTyp : C0Parser s Typ :=
  first [
    (do kw_int    ; return Typ.int   )
  , (do kw_bool   ; return Typ.bool  )
  , (do kw_char   ; return Typ.char  )
  , (do kw_string ; return Typ.string)
  , (do kw_void   ; return Typ.void  )
  , (do let name ← typeIdent tydefs; return Typ.tydef name)
  , (do kw_struct; ws; let name ← rawIdent; return Typ.struct name)
  ]

def typ : C0Parser s Typ :=
  withContext "<type>" do
  -- parse a simple type
  let t ← simpleTyp
  -- parse as many * and [] as we can
  foldl (return t)
    (fun t => withBacktrackingUntil ws fun () =>
      (do char '*'; return Typ.ptr t)
      <|> (do char '['; ws; char ']'; return Typ.arr t) )
end

def unop.int : C0Parser s UnOp.Int :=
  first [
    (do withBacktracking (do char '-'; notFollowedBy (char '-'); notFollowedBy (char '>')); return .neg)
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
    (do wholeString "<="; return .le)
  , (do char '<'; return .lt)
  , (do wholeString ">="; return .ge)
  , (do char '>'; return .gt)
  ]

def binop.cmp.prec_7 : C0Parser s BinOp.Cmp :=
  first [
    (do wholeString "=="; return .eq)
  , (do wholeString "!="; return .ne)
  ]

def binop.int.prec_6 : C0Parser s BinOp.Int :=
  withBacktracking (do char '&'; notFollowedBy (char '&'); return .and)

def binop.int.prec_5 : C0Parser s BinOp.Int :=
  (do char '^'; return .xor)

def binop.int.prec_4 : C0Parser s BinOp.Int :=
  withBacktracking (do char '|'; notFollowedBy (char '|'); return .or)

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
    (do withBacktracking (do char '='; notFollowedBy <| char '='); return .eq)
<|> (do let op ← withBacktrackingUntil binop.int
                    (fun op => do char '='; return op)
        return .aseq op)

def postop : C0Parser s PostOp :=
    (do wholeString "++"; return .incr)
<|> (do wholeString "--"; return .decr)

mutual
partial def expr.prec_13 : C0Parser s Expr :=
  withContext "<expr-13>" <|
  foldl (left <* ws) (fun lhs => right lhs <* ws)
where
  left : C0Parser s Expr :=
    first [
      (do let v ← num   ; return .num v)
    , (do let c ← chrlit; return .char c)
    , (do let s ← strlit; return .str s)
    , (do kw_true       ; return .«true»)
    , (do kw_false      ; return .«false»)
    , (do kw_NULL       ; return .null)
    , (do kw_result     ; return .result)
    , (do kw_length; ws; char '('; ws
          let e ← expr
          ws; char ')'
          return .length e)
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
          (do withBacktrackingUntil ws (fun () => char '('); ws
              let args ← sepBy (do ws; char ','; ws) expr
              ws; char ')'
              return .app name args.toList)
          <|>
          (return .var name))
    , (do char '('; ws; let e ← expr; ws; char ')'; return e)
    ]
  right (lhs) := do
    first [
      (do char '.'; ws; let f ← rawIdent
          return (.dot lhs f))
    , (do wholeString "->"; ws; let f ← rawIdent
          return (.arrow lhs f))
    , (do char '['; ws; let e ← expr; ws; char ']'
          return (.index lhs e))
    ]

partial def expr.prec_12 : C0Parser s Expr :=
  withContext "<expr-12>" <|
  first [
    (do let op ← unop; ws; let e ← expr.prec_12; return .unop op e)
  , (do char '*'; ws; let e ← expr.prec_12; return .deref e)
  , expr.prec_13
  ]

partial def expr.prec_11 : C0Parser s Expr :=
  withContext "<expr-11>" <|
  foldl (expr.prec_12 <* ws) (fun lhs => do
    let op ← binop.int.prec_11; ws; let rhs ← expr.prec_12; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_10 : C0Parser s Expr :=
  withContext "<expr-10>" <|
  foldl (expr.prec_11 <* ws) (fun lhs => do
    let op ← binop.int.prec_10; ws; let rhs ← expr.prec_11; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_9 : C0Parser s Expr :=
  withContext "<expr-9>" <|
  foldl (expr.prec_10 <* ws) (fun lhs => do
    let op ← binop.int.prec_9; ws; let rhs ← expr.prec_10; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_8 : C0Parser s Expr :=
  withContext "<expr-8>" <|
  foldl (expr.prec_9 <* ws) (fun lhs => do
    let op ← binop.cmp.prec_8; ws; let rhs ← expr.prec_9; ws
    return (.binop (.cmp op) lhs rhs))

partial def expr.prec_7 : C0Parser s Expr :=
  withContext "<expr-7>" <|
  foldl (expr.prec_8 <* ws) (fun lhs => do
    let op ← binop.cmp.prec_7; ws; let rhs ← expr.prec_8; ws
    return (.binop (.cmp op) lhs rhs))

partial def expr.prec_6 : C0Parser s Expr :=
  withContext "<expr-6>" <|
  foldl (expr.prec_7 <* ws) (fun lhs => do
    let op ← binop.int.prec_6; ws; let rhs ← expr.prec_7; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_5 : C0Parser s Expr :=
  withContext "<expr-5>" <|
  foldl (expr.prec_6 <* ws) (fun lhs => do
    let op ← binop.int.prec_5; ws; let rhs ← expr.prec_6; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_4 : C0Parser s Expr :=
  withContext "<expr-4>" <|
  foldl (expr.prec_5 <* ws) (fun lhs => do
    let op ← binop.int.prec_4; ws; let rhs ← expr.prec_5; ws
    return (.binop (.int op) lhs rhs))

partial def expr.prec_3 : C0Parser s Expr :=
  withContext "<expr-3>" <|
  foldl (expr.prec_4 <* ws) (fun lhs => do
    let op ← binop.bool.prec_3; ws; let rhs ← expr.prec_4; ws
    return (.binop (.bool op) lhs rhs))

partial def expr.prec_2 : C0Parser s Expr :=
  withContext "<expr-2>" <|
  foldl (expr.prec_3 <* ws) (fun lhs => do
    let op ← binop.bool.prec_2; ws; let rhs ← expr.prec_3; ws
    return (.binop (.bool op) lhs rhs))

partial def expr.prec_1 : C0Parser s Expr :=
  withContext "<expr-1>" do
  let lhs ← expr.prec_2
  -- Note whitespace already has been consumed
  (do char '?'; ws
      let tt ← expr.prec_1; ws
      char ':'; ws; let ff ← expr.prec_1;
      return .ternop lhs tt ff)
  <|> (do return lhs)

partial def expr : C0Parser s Expr :=
  withContext "<expr>" expr.prec_1
end

mutual
partial def lvalue.prec_13.left : C0Parser s LValue :=
  (do char '('; ws; let lv ← lvalue; ws; char ')'; return lv)
  <|>
  (do let name ← ident tydefs; return .var name)

partial def lvalue.prec_13 : C0Parser s LValue :=
  foldl lvalue.prec_13.left
    (fun lv =>
      withBacktrackingUntil ws
      (fun () => first [
        (do
        char '.'; ws
        let field ← rawIdent
        return (.dot lv field))
      , (do
        wholeString "->"; ws
        let field ← rawIdent
        return (.arrow lv field))
      , (do
        char '['; ws; let index ← expr tydefs; char ']'
        return (.index lv index))
      ])
    )

partial def lvalue.prec_12 : C0Parser s LValue :=
  (do char '*'; ws; let lv ← lvalue.prec_12; return .deref lv)
  <|> lvalue.prec_13

partial def lvalue : C0Parser s LValue :=
  withContext "<lvalue>" (lvalue.prec_12)

end

def spec : C0Parser s Spec :=
  withContext "<spec>" <|
  first [
      (do kw_requires  ; ws; let e ← expr tydefs; ws; char ';'; return .requires e  )
    , (do kw_ensures   ; ws; let e ← expr tydefs; ws; char ';'; return .ensures e   )
    , (do kw_loop_invar; ws; let e ← expr tydefs; ws; char ';'; return .loop_invar e)
    , (do kw_assert    ; ws; let e ← expr tydefs; ws; char ';'; return .assert e    )
    ]

def anno : C0Parser s Anno :=
  withContext "<anno>" <|
      (do wholeString "//@"
          ws_no_newline
          let specs ← sepBy ws_no_newline (spec tydefs)
          ws_no_newline; char '\n'
          return .line specs.toList)
  <|> (do wholeString "/*@"
          let specs ← sepBy ws (spec tydefs)
          ws; wholeString "@*/"
          return .block specs.toList)


mutual
partial def control : C0Parser s Control :=
  first [
    (do kw_if; ws; char '('; ws; let cond ← expr tydefs; ws; char ')'; ws
        let tt ← stmt
        let ff ← option (do withBacktracking (do ws; kw_else); ws; stmt)
        return Control.ite cond tt (ff.getD (.block [] [])))
  , (do kw_while; ws; char '('; ws; let cond ← expr tydefs; ws; char ')'; ws
        let body ← stmt
        return Control.«while» cond body)
  , (do kw_for; ws; char '('; ws
        let init ← option simp; ws; char ';'; ws
        let cond ← expr tydefs; ws; char ';'; ws
        let step ← option simp; ws
        char ')'; ws
        let body ← stmt
        return Control.«for» init cond step body)
  , (do kw_return; ws; let e ← option (expr tydefs); ws; char ';'
        return Control.«return» e)
  , (do kw_assert; ws; char '('; ws; let e ← expr tydefs; ws; char ')'; ws; char ';'
        return Control.assert e)
  , (do kw_error; ws; char '('; ws; let e ← expr tydefs; ws; char ')'; ws; char ';'
        return Control.error e)
  ]

partial def simp : C0Parser s Simp :=
  first [
    (do
      let type ← typ tydefs; ws
      let name ← ident tydefs; ws;
      let init ← option (do char '='; ws; expr tydefs)
      return .decl type name init)
  , withBacktrackingUntil
    -- post-op needs a higher precedence lvalue than asnop
      (lvalue.prec_13 tydefs <* ws) (fun lv =>
      do let op ← postop; return .post lv op)
  , withBacktrackingUntil (lvalue tydefs <* ws) (fun lv =>
      do let op ← asnop; ws; let v ← expr tydefs; return .assn lv op v)
  , (do let e ← expr tydefs; return .exp e)
  ]

partial def block : C0Parser s Stmt := do
  char '{'; ws
  let body ← sepBy ws stmt
  let annos ← sepBy ws (anno tydefs)
  ws; char '}'
  return .block body.toList annos.toList

partial def stmt : C0Parser s Stmt :=
  first [
    (do let s ← simp; ws; char ';'; return .simp s)
  , (do return .ctrl (←control))
  , block
  , (do let a ← anno tydefs; ws; let s ← stmt; return .anno a s)
  ]

end

def field : C0Parser s Field :=
  withContext "<struct-field>" do
  let type ← typ tydefs
  ws
  let name ← rawIdent
  ws; char ';'
  return ⟨type, name⟩

def sdef : C0Parser s SDef :=
  withContext "<struct-def>" do
  let name ← withBacktracking do
    kw_struct; ws
    let name ← rawIdent
    ws; char '{'
    pure name
  ws
  let fields ← sepBy ws (field tydefs)
  ws; char '}'; ws; char ';'
  return ⟨name, fields.toList⟩

def sdecl : C0Parser s SDecl :=
  withContext "<struct-decl>" <|
  withBacktracking do
  kw_struct; ws
  let name ← rawIdent; ws
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
  ws; char ')'; ws
  let annos ← sepBy ws (anno tydefs)
  return ⟨type, name, params.toList, annos.toList⟩

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

def cdir : C0Parser s Directive :=
  withContext "<directive>" do
  char '#'
  (do kw_use; ws_no_newline
      let l ← liblit; ws_no_newline
      char '\n'
      return .use_lib l)
  <|> (do kw_use; ws_no_newline
          let l ← strlit; ws_no_newline
          char '\n'
          return .use_str l)
  <|> (do dropMany (do let _ ← charMatching (· ≠ '\n'))
          return .unknown)

def gdecl : C0Parser s GDecl :=
  first
  [ do return .tydef (← tydef tydefs)
  , do return .sdecl (← sdecl)
  , do return .sdef  (← sdef  tydefs)
  , do
    let sig ← signature tydefs
    (return .fdecl (← fdecl sig))
    <|> (return .fdef (← fdef tydefs sig))
  , do return .cdir (← cdir)
  ]

partial def prog (tydefs : Std.RBSet Symbol compare := .empty) : C0Parser s (Prog × Std.RBSet Symbol compare) := do
  ws
  let (gdecls,tydefs) ← aux tydefs #[]
  return (gdecls.toList,tydefs)
where aux tydefs acc :=
  (do eof; return (acc,tydefs))
  <|> (do
    let g ← gdecl tydefs
    ws
    let tydefs := match g with | .tydef ⟨_, i⟩ => tydefs.insert i | _ => tydefs
    aux tydefs (acc.push g))

partial def directives : C0Parser s (List Directive) := do
  ws
  let cds ← aux #[]
  return cds.toList
where aux acc :=
  (do eof; return acc)
  <|> (do let cd ← cdir; ws; aux (acc.push cd))
  <|> (return acc)
