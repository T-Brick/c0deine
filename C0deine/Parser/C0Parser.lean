import C0deine.AuxDefs
import C0deine.Parser.Cst
import C0deine.Parser.C0Lexer
import C0deine.Context.Context
import C0deine.Utils.Int32

namespace C0deine.Parser

open Megaparsec Parsec Common

abbrev C0Parser := ParsecT Context (OfTokenArray Token) (TokenArraySource Token) Unit

namespace C0Parser

open Cst

variable (tydefs : Std.RBSet Symbol Ord.compare)

def rawIdent : C0Parser Ident :=
  label "<ident>" <| attempt do
  match ← anySingle with
  | Token.ident id =>
    return ← liftM <| Symbol.symbol id
  | _ => failure

def typeIdent : C0Parser Ident :=
  label "<type-ident>" <| attempt do
  let id ← rawIdent
  if tydefs.contains id then
    return id
  else
    failure

def ident : C0Parser Ident :=
  label "<ident>" <| attempt do
  let id ← rawIdent
  if tydefs.contains id then
    failure
  else
    return id

def num : C0Parser Int32 :=
  label "<number>" <| do
  let n : String ← attempt (do
    match ← anySingle with
    | Token.num n =>
      return n.str
    | _ => failure)
  match Int32.ofInt? n.toInt! with
  | .none => failure
  | .some i => return i

abbrev kw (k : Token.Keyword) : C0Parser Unit := void <| single (Token.keyword k)
abbrev sc (c : Token.Special) : C0Parser Unit := void <| single (Token.special c)

mutual
def simpleTyp : C0Parser Typ :=
  choice [
    (do kw .int ; return Typ.int)
  , (do kw .bool; return Typ.bool)
  , (do kw .void; return Typ.void)
  , (do let name ← typeIdent tydefs; return Typ.tydef name)
  , (do kw .struct; let name ← rawIdent; return Typ.struct name)
  ]

def typ : C0Parser Typ :=
  label "<type>" do
  -- parse a simple type
  let t ← simpleTyp
  -- parse as many * and [] as we can
  foldl t (fun t =>
    choice [
      (do sc .star; return Typ.ptr t)
    , (do sc .lbrack; sc .rbrack; return Typ.arr t)
    ]
  )
end

def unop.int : C0Parser UnOp.Int :=
  choice [
    (do sc .minus return .neg)
  , (do sc .tilde; return .not)
  ]

def unop.bool : C0Parser UnOp.Bool :=
  (do sc .bang; return .not)

def unop : C0Parser UnOp :=
  choice [
    (do let op ← unop.int; return .int op)
  , (do let op ← unop.bool; return .bool op)
  ]

def binop.int.prec_11 : C0Parser BinOp.Int :=
  choice [
    (do sc .star; return .times)
  , (do sc .div; return .div)
  , (do sc .mod; return .mod)
  ]

def binop.int.prec_10 : C0Parser BinOp.Int :=
  choice [
    (do sc .plus; return .plus)
  , (do sc .minus; return .minus)
  ]

def binop.int.prec_9 : C0Parser BinOp.Int :=
  choice [
    (do sc .lsh; return .lsh)
  , (do sc .rsh; return .rsh)
  ]

def binop.cmp.prec_8 : C0Parser BinOp.Cmp :=
  choice [
    (do sc .le; return .le)
  , (do sc .lt; return .lt)
  , (do sc .ge; return .ge)
  , (do sc .gt; return .gt)
  ]

def binop.cmp.prec_7 : C0Parser BinOp.Cmp :=
  choice [
    (do sc .eq; return .eq)
  , (do sc .ne; return .ne)
  ]

def binop.int.prec_6 : C0Parser BinOp.Int :=
  (do sc .and; return .and)

def binop.int.prec_5 : C0Parser BinOp.Int :=
  (do sc .xor; return .xor)

def binop.int.prec_4 : C0Parser BinOp.Int :=
  (do sc .or; return .or)

def binop.bool.prec_3 : C0Parser BinOp.Bool :=
  (do sc .andand; return .and)

def binop.bool.prec_2 : C0Parser BinOp.Bool :=
  (do sc .oror; return .or)

def binop.int : C0Parser BinOp.Int :=
  choice [
    binop.int.prec_11 , binop.int.prec_10 , binop.int.prec_9
  , binop.int.prec_6  , binop.int.prec_5  , binop.int.prec_4
  ]

def asnop : C0Parser AsnOp :=
    (do sc .asn; return .eq)
<|> (do sc .plusasn; return .aseq .plus)
<|> (do sc .minusasn; return .aseq .minus)
<|> (do sc .starasn; return .aseq .times)
<|> (do sc .divasn; return .aseq .div)
<|> (do sc .modasn; return .aseq .mod)
<|> (do sc .lshasn; return .aseq .lsh)
<|> (do sc .rshasn; return .aseq .rsh)
<|> (do sc .andasn; return .aseq .and)
<|> (do sc .orasn; return .aseq .or)
<|> (do sc .xorasn; return .aseq .xor)

def postop : C0Parser PostOp :=
    (do sc .plusplus; return .incr)
<|> (do sc .minusminus; return .decr)

mutual
partial def expr.prec_13 : C0Parser Expr :=
  label "<expr-13>" <| do
  foldl (← left) (fun lhs => right lhs)
where
  left : C0Parser Expr :=
    choice [
      (do sc .lparen; let e ← expr; sc .rparen; return e)
    , (do let v ← num; return .num v)
    , (do kw .true; return .«true»)
    , (do kw .false; return .«false»)
    , (do kw .NULL; return .null)
    , (do kw .alloc; sc .lparen
          let ty ← typ tydefs
          sc .rparen
          return .alloc ty)
    , (do kw .alloc_array; sc .lparen
          let ty ← typ tydefs
          sc .comma
          let e ← expr
          sc .rparen
          return .alloc_array ty e)
    , (do let name ← ident tydefs
          (do sc .lparen
              let args ← sepEndByP (sep := sc .comma) expr
              sc .rparen
              return .app name args)
          <|>
          (return .var name))
    ]
  right (lhs) := do
    choice [
      (do sc .dot; let f ← rawIdent
          return (.dot lhs f))
    , (do sc .arrow; let f ← rawIdent
          return (.arrow lhs f))
    , (do sc .lbrack; let e ← expr; sc .rbrack
          return (.index lhs e))
    ]

partial def expr.prec_12 : C0Parser Expr :=
  label "<expr-12>" <|
  choice [
    (do let op ← unop; let e ← expr.prec_12; return .unop op e)
  , (do sc .star; let e ← expr.prec_12; return .deref e)
  , expr.prec_13
  ]

partial def expr.prec_11 : C0Parser Expr :=
  label "<expr-11>" <| do
  foldl (← expr.prec_12) (fun lhs => do
    let op ← binop.int.prec_11; let rhs ← expr.prec_12
    return (.binop (.int op) lhs rhs))

partial def expr.prec_10 : C0Parser Expr :=
  label "<expr-10>" <| do
  foldl (← expr.prec_11) (fun lhs => do
    let op ← binop.int.prec_10; let rhs ← expr.prec_11
    return (.binop (.int op) lhs rhs))

partial def expr.prec_9 : C0Parser Expr :=
  label "<expr-9>" <| do
  foldl (← expr.prec_10) (fun lhs => do
    let op ← binop.int.prec_9; let rhs ← expr.prec_10
    return (.binop (.int op) lhs rhs))

partial def expr.prec_8 : C0Parser Expr :=
  label "<expr-8>" <| do
  foldl (← expr.prec_9) (fun lhs => do
    let op ← binop.cmp.prec_8; let rhs ← expr.prec_9
    return (.binop (.cmp op) lhs rhs))

partial def expr.prec_7 : C0Parser Expr :=
  label "<expr-7>" <| do
  foldl (← expr.prec_8) (fun lhs => do
    let op ← binop.cmp.prec_7; let rhs ← expr.prec_8
    return (.binop (.cmp op) lhs rhs))

partial def expr.prec_6 : C0Parser Expr :=
  label "<expr-6>" <| do
  foldl (← expr.prec_7) (fun lhs => do
    let op ← binop.int.prec_6; let rhs ← expr.prec_7
    return (.binop (.int op) lhs rhs))

partial def expr.prec_5 : C0Parser Expr :=
  label "<expr-5>" <| do
  foldl (← expr.prec_6) (fun lhs => do
    let op ← binop.int.prec_5; let rhs ← expr.prec_6
    return (.binop (.int op) lhs rhs))

partial def expr.prec_4 : C0Parser Expr :=
  label "<expr-4>" <| do
  foldl (← expr.prec_5) (fun lhs => do
    let op ← binop.int.prec_4; let rhs ← expr.prec_5
    return (.binop (.int op) lhs rhs))

partial def expr.prec_3 : C0Parser Expr :=
  label "<expr-3>" <| do
  foldl (← expr.prec_4) (fun lhs => do
    let op ← binop.bool.prec_3; let rhs ← expr.prec_4
    return (.binop (.bool op) lhs rhs))

partial def expr.prec_2 : C0Parser Expr :=
  label "<expr-2>" <| do
  foldl (← expr.prec_3) (fun lhs => do
    let op ← binop.bool.prec_2; let rhs ← expr.prec_3
    return (.binop (.bool op) lhs rhs))

partial def expr.prec_1 : C0Parser Expr :=
  label "<expr-1>" do
  let lhs ← expr.prec_2
  -- Note whitespace already has been consumed
  (do sc .question
      let tt ← expr.prec_1
      sc .colon; let ff ← expr.prec_1;
      return .ternop lhs tt ff)
  <|> (do return lhs)

partial def expr : C0Parser Expr :=
  label "<expr>" expr.prec_1
end

mutual
partial def lvalue.prec_13.left : C0Parser LValue :=
  (do sc .lparen; let lv ← lvalue; sc .rparen; return lv)
  <|>
  (do let name ← ident tydefs; return .var name)

partial def lvalue.prec_13 : C0Parser LValue := do
  foldl (← lvalue.prec_13.left)
    (fun lv =>
      choice [
        (do
        sc .dot
        let field ← rawIdent
        return (.dot lv field))
      , (do
        sc .arrow
        let field ← rawIdent
        return (.arrow lv field))
      , (do
        sc .lbrack; let index ← expr tydefs; sc .rbrack
        return (.index lv index))
      ]
    )

partial def lvalue.prec_12 : C0Parser LValue :=
  (do sc .star; let lv ← lvalue.prec_12; return .deref lv)
  <|> lvalue.prec_13

partial def lvalue : C0Parser LValue :=
  label "<lvalue>" (lvalue.prec_12)
    
end


mutual
partial def control : C0Parser Control :=
  choice [
    (do kw .if; sc .lparen; let cond ← expr tydefs; sc .rparen
        let tt ← stmt
        let ff ← option (do kw .else; stmt)
        return Control.ite cond tt (ff.getD (.block [])))
  , (do kw .while; sc .lparen; let cond ← expr tydefs; sc .rparen
        let body ← stmt
        return Control.«while» cond body)
  , (do kw .for; sc .lparen
        let init ← option simp; sc .semi
        let cond ← expr tydefs; sc .semi
        let step ← option simp
        sc .rparen
        let body ← stmt
        return Control.«for» init cond step body)
  , (do kw .return; let e ← option (expr tydefs); sc .semi
        return Control.«return» e)
  , (do kw .assert; sc .lparen; let e ← expr tydefs; sc .rparen; sc .semi
        return Control.assert e)
  ]

partial def simp : C0Parser Simp :=
  choice [
    (do
      let type ← typ tydefs
      let name ← ident tydefs;
      let init ← option (do sc .asn; expr tydefs)
      return .decl type name init)
  , (do
      -- post-op needs a higher precedence lvalue than asnop
      let lv ← attempt (lvalue.prec_13 tydefs <* lookAhead postop)
      let op ← postop; return .post lv op)
  , (do
      let lv ← attempt (lvalue tydefs <* lookAhead asnop)
      do let op ← asnop; let v ← expr tydefs; return .assn lv op v)
  , (do let e ← expr tydefs; return .exp e)
  ]

partial def block : C0Parser Stmt := do
  sc .lbrace
  let body ← many' stmt
  sc .rbrace
  return .block body

partial def stmt : C0Parser Stmt :=
  choice [
    (do let s ← simp; sc .semi; return .simp s)
  , (do return .ctrl (←control))
  , block
  ]

end

def field : C0Parser Field :=
  label "<struct-field>" do
  let type ← typ tydefs
  let name ← rawIdent
  sc .semi
  return ⟨type, name⟩

def sdef : C0Parser SDef :=
  label "<struct-def>" do
  let name ← attempt do
    kw .struct
    let name ← rawIdent
    sc .lbrace
    return name
  let fields ← many' (field tydefs)
  sc .rbrace; sc .semi
  return ⟨name, fields⟩

def sdecl : C0Parser SDecl :=
  label "<struct-decl>" <|
  attempt do
  kw .struct
  let name ← rawIdent
  sc .semi
  return ⟨name⟩

def tydef : C0Parser TyDef :=
  label "<type-def>" do
  kw .typedef
  let type ← typ tydefs
  let name ← ident tydefs
  sc .semi
  return ⟨type, name⟩

def param : C0Parser Param := do
  let type ← typ tydefs
  let name ← ident tydefs
  return ⟨type, name⟩

private def signature : C0Parser FDecl :=
  label "<func-sig>" do
  let type ← typ tydefs
  let name ← ident tydefs
  sc .lparen
  let params ← sepEndByP (sep := sc .comma) (param tydefs)
  sc .rparen
  return ⟨type, name, params⟩

def fdecl (sig : FDecl) : C0Parser FDecl :=
  label "<func-decl>" <| do
  sc .semi
  return sig

def fdef (sig : FDecl) : C0Parser FDef :=
  label "<func-def>" do
  let body ← block tydefs
  return {sig with body}

def gdecl : C0Parser GDecl :=
  choice
  [ do return .tydef (← tydef tydefs)
  , do return .sdecl (← sdecl)
  , do return .sdef  (← sdef  tydefs)
  , do
    let sig ← signature tydefs
    (return .fdecl (← fdecl sig)) 
    <|> (return .fdef (← fdef tydefs sig))
  ]

partial def prog : C0Parser (Prog × Std.RBSet Symbol compare) := do
  let (gdecls,tydefs) ← aux tydefs #[]
  return (gdecls.toList,tydefs)
where aux tydefs acc :=
  (do eof; return (acc,tydefs))
  <|> (do
    let g ← gdecl tydefs
    let tydefs := match g with | .tydef ⟨_, i⟩ => tydefs.insert i | _ => tydefs
    aux tydefs (acc.push g))

nonrec def parse (s : String) :=
  show ExceptT String Context _ from do
  let toks ← Except.mapError (toString) (parseT (m := Id) C0Lexer.tokens s)
  ExceptT.adapt (toString) do
  let (prog, tydefs) ← (
    show Context (Except _ _) from
      parseT (prog tydefs) toks)
  return (prog, tydefs)
