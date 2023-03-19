import Std
import Parser

import C0deine.Utils.Context
import C0deine.Parser.Cst
import C0deine.AuxDefs

open Parser

namespace C0deine.Parser

abbrev C0Parser := SimpleParserT Substring Char (ExceptT (Parser.Error.Simple Substring Char) Context)

namespace C0Parser

open Cst

instance : MonadLiftT Context C0Parser :=
  show MonadLiftT _ (StateT _ _) from inferInstance
instance : Inhabited (C0Parser α) := ⟨throwUnexpected⟩

variable (tydefs : Std.RBSet Symbol Ord.compare)

private def char (c : Char) : C0Parser Unit := do let _ ← Char.char c
private def chars (s : String) : C0Parser Unit := do let _ ← Char.chars s

def rawIdent : C0Parser Ident := do
  let c ← tokenFilter (fun c => c.isAlpha || c = '_')
  let str ← foldl String.push (return c.toString) (tokenFilter (fun c => c.isAlphanum || c = '_'))
  return ← liftM <| Symbol.symbol str

def typeIdent : C0Parser Ident := do
  let id ← rawIdent
  if tydefs.contains id then
    return id
  else
    throwUnexpected

def ident : C0Parser Ident := do
  let id ← rawIdent
  if tydefs.contains id then
    throwUnexpected
  else
    return id

def intmin : UInt32 := 0x80000000
example : intmin.val = 1 <<< 31 := rfl

def num : C0Parser UInt32 := do
  dec <|> hex <|> (do let _ ← chars "-2147483648"; return intmin)
where
  dec : C0Parser UInt32 := do
    let digs ← foldl String.push
      (do let c ← tokenFilter (fun c => '1' ≤ c && c ≤ '9'); return c.toString)
      (tokenFilter (fun c => '0' ≤ c && c ≤ '9'))
    let nat := Nat.ofDigits? 10 digs |>.get!
    if h : nat < intmin.val then
      return ⟨nat, Nat.lt_trans h intmin.val.isLt⟩
    else
      throwUnexpected -- fun () => s!"int literal {digs} is too big"
  hex : C0Parser UInt32 := do
    char '0'
    let _ ← (Char.char 'x' <|> Char.char 'X')
    let digs ← foldl String.push (pure "") (tokenFilter (fun c => '0' ≤ c && c ≤ '9' || 'a' ≤ c && c ≤ 'f' || 'A' ≤ c && c ≤ 'F'))
    if digs.length = 0 then
      throwUnexpected -- fun () => "expected [0-9a-fA-F]"
    let nat := Nat.ofDigits? 16 digs |>.get!
    if h : nat < intmin.val then
      return ⟨nat, Nat.lt_trans h intmin.val.isLt⟩
    else
      throwUnexpected -- fun () => s!"int literal 0x{digs} is too big"


def lineComment : C0Parser Unit := do
  chars "//"
  dropMany (tokenFilter (· ≠ '\n'))

partial def blockComment : C0Parser Unit := do
  chars "/*"
  dropMany (
    (do let _ ← tokenFilter (¬ · ∈ ['/', '*']))
    <|> (do char '*'; notFollowedBy (do char '/'))
    <|> (do char '/'; notFollowedBy (do char '*'))
    <|> blockComment)
  chars "*/"

def ws : C0Parser Unit :=
  dropMany (
    (do let _ ← tokenFilter (· ∈ [' ', '\n', '\t', '\r', '\u0011', '\u0012']))
    <|> lineComment
    <|> blockComment)

@[inline] def keyword (s : String) : C0Parser Unit := do
  /- keywords should not be followed by alphanums-/
  chars s
  notFollowedBy (tokenFilter (·.isAlphanum))

mutual
def simpleTyp : C0Parser Typ :=
      (do keyword "int" ; return Typ.int)
  <|> (do keyword "bool"; return Typ.bool)
  <|> (do keyword "void"; return Typ.void)
  <|> (do let name ← ident tydefs; return Typ.tydef name)
  <|> (do keyword "struct"; ws; let name ← ident tydefs; return Typ.struct name)

def typ : C0Parser Typ := do
  -- parse a simple type
  let t ← simpleTyp
  -- parse as many * and [] as we can
  foldl (fun t (f : Typ → Typ) => f t)
    (return t)
    (do
      ws
      (do char '*'; return Typ.ptr)
      <|> (do char '['; ws; char ']'; return Typ.arr) )
end

def unop.int : C0Parser UnOp.Int :=
  (do char '-'; notFollowedBy (char '-'); return .neg)
  <|> (do char '~'; return .not)

def unop.bool : C0Parser UnOp.Bool :=
  (do char '!'; return .neg)

def unop : C0Parser UnOp :=
    (do let op ← unop.int; return .int op)
<|> (do let op ← unop.bool; return .bool op)

def binop.int : C0Parser BinOp.Int :=
    (do char '+'; return .plus)
<|> (do char '-'; notFollowedBy (char '-'); return .minus)
<|> (do char '*'; return .times)
<|> (do char '/'; return .div)
<|> (do char '%'; return .mod)
<|> (do char '&'; return .and)
<|> (do char '^'; return .xor)
<|> (do char '|'; return .or)
<|> (do chars "<<"; return .lsh)
<|> (do chars ">>"; return .rsh)

def binop.cmp : C0Parser BinOp.Cmp :=
    (do char '<'; return .lt)
<|> (do chars "<="; return .le)
<|> (do char '>'; return .gt)
<|> (do chars ">="; return .ge)
<|> (do chars "=="; return .eq)
<|> (do chars "!="; return .ne)

def binop.bool : C0Parser BinOp.Bool :=
    (do chars "&&"; return .and)
<|> (do chars "||"; return .or)

def binop : C0Parser BinOp :=
    (do let op ← binop.int; return .int op)
<|> (do let op ← binop.cmp; return .cmp op)
<|> (do let op ← binop.bool; return .bool op)

def asnop : C0Parser AsnOp :=
    (do char '='; return .eq)
<|> (do let op ← binop.int; char '='; return .aseq op)

def postop : C0Parser PostOp :=
    (do chars "++"; return .incr)
<|> (do chars "--"; return .decr)

mutual
partial def lvalue : C0Parser LValue :=
  -- parse a simple lv (always an ident or )
  (do let name ← ident tydefs; return .var name)
  <|> (do
    let lv ← lvalue
    ws
    (do
      char '.'; ws
      let field ← ident tydefs
      return .dot lv field)
    <|> (do
      chars "->"; ws
      let field ← ident tydefs
      return .arrow lv field)
    <|> (do
      char '*'; ws
      return .deref lv)
    <|> (do
      char '['; ws; let index ← expr; char ']'
      return .index lv index
    )
  )

partial def expr._1 : C0Parser Expr :=
    (do char '('; let e ← expr; char ')'; return e)
<|> (do let v ← num; return .num v)
<|> (do keyword "true"; return .«true»)
<|> (do keyword "false"; return .«false»)
<|> (do keyword "NULL"; return .null)
<|> (do keyword "alloc"; ws; char '('; ws
        let ty ← typ tydefs
        ws; char ')'
        return .alloc ty)
<|> (do keyword "alloc_array"; ws; char '('; ws
        let ty ← typ tydefs
        ws; char ','; ws
        let e ← expr
        ws; char ')'
        return .alloc_array ty e)
<|> (do let name ← ident tydefs
        (do ws; char '('; ws
            let args ← foldl (Array.push)
              (do let e ← expr; return #[e])
              (do ws; char ','; ws; expr)
            char ')'
            return .app name args.toList)
        <|>
        (return .var name))

partial def expr._1.right : C0Parser Expr := do
  foldl (fun x (f : Expr → Expr) => f x) expr._1
    (   (do ws; char '.'  ; ws; let f ← ident tydefs; return (.dot · f))
    <|> (do ws; chars "->"; ws; let f ← ident tydefs; return (.arrow · f))
    <|> (do ws; char '['  ; ws; let e ← expr; return (.index · e)))

partial def expr : C0Parser Expr :=
    (do let op ← unop; ws; let e ← expr; return .unop op e)
<|> (do let l  ← expr; ws; let op ← binop; ws; let r ← expr; return .binop op l r)
<|> (do let cond ← expr; ws; char '?'; ws; let tt ← expr; ws; char ':'; ws; let ff ← expr
        return .ternop cond tt ff)
<|> (do char '*'; return .deref (← expr))
end

mutual
partial def control : C0Parser Control :=
    (do keyword "if"; ws; char '('; ws; let cond ← expr tydefs; ws; char ')'; ws
        let tt ← stmt
        let ff ← option? (do ws; keyword "else"; stmt)
        return Control.ite cond tt (ff.getD (.block [])))
<|> (do keyword "while"; ws; char '('; ws; let cond ← expr tydefs; ws; char ')'; ws
        let body ← stmt
        return Control.«while» cond body)
<|> (do keyword "for"; ws; char '('; ws;
        let init ← simp; ws; char ';'; ws; let cond ← expr tydefs; ws; char ';'; ws; let step ← option? simp; ws; char ')'; ws
        let body ← stmt
        return Control.«for» init cond step body)
<|> (do keyword "return"; ws; let e ← option? (expr tydefs); ws; char ';'
        return Control.«return» e)
<|> (do keyword "assert"; ws; let e ← expr tydefs; ws; char ';'
        return Control.assert e)

partial def simp : C0Parser Simp :=
    (do let type ← typ tydefs; ws
        let name ← ident tydefs; ws;
        let init ← option? (do char '='; ws; expr tydefs); ws; char ';'
        return .decl type name init)
<|> (do let lv ← lvalue tydefs; ws
        let op ← asnop; ws
        let v ← expr tydefs
        return .assn lv op v)
<|> (do let lv ← lvalue tydefs; ws
        let op ← postop
        return .post lv op)
<|> (do let e ← expr tydefs; return .exp e)

partial def block : C0Parser Stmt := do
  char '{'; ws
  let body ← sepBy ws stmt
  ws; char '}'
  return .block body.toList

partial def stmt : C0Parser Stmt :=
    (do return .simp (←simp))
<|> (do return .ctrl (←control))
<|> block
end

def field : C0Parser Field := do
  let type ← typ tydefs
  ws
  let name ← ident tydefs
  char ';'
  return ⟨type, name⟩

def sdef : C0Parser SDef := do
  keyword "struct"; ws
  let name ← ident tydefs; ws
  char '{'; ws
  let fields ← sepBy ws (field tydefs)
  ws; char '}'
  return ⟨name, fields.toList⟩

def sdecl : C0Parser SDecl := do
  keyword "struct"; ws
  let name ← ident tydefs; ws
  char ';'
  return ⟨name⟩

def tydef : C0Parser TyDef := do
  keyword "typedef"; ws
  let type ← typ tydefs; ws
  let name ← ident tydefs; ws
  char ';'
  return ⟨type, name⟩

def param : C0Parser Param := do
  let type ← typ tydefs; ws
  let name ← ident tydefs
  return ⟨type, name⟩

private def signature : C0Parser FDecl := do
  let type ← typ tydefs; ws
  let name ← ident tydefs; ws
  char '('; ws
  let params ← sepBy (do ws; char ','; ws) (param tydefs)
  ws; char ')'
  return ⟨type, name, params.toList⟩

def fdef : C0Parser FDef := do
  let sig ← signature tydefs
  ws
  let body ← block tydefs
  return {sig with body}

def fdecl : C0Parser FDecl := do
  let sig ← signature tydefs
  ws; char ';'
  return sig

def gdecl : C0Parser GDecl :=
    (do return .fdecl (← fdecl tydefs)) 
<|> (do return .fdef  (← fdef  tydefs))
<|> (do return .tydef (← tydef tydefs))
<|> (do return .sdecl (← sdecl tydefs))
<|> (do return .sdef  (← sdef  tydefs)) 

partial def prog : C0Parser (List GDecl) := do
  let gdecls ← aux (Std.RBSet.empty) #[]
  return gdecls.toList
where aux tydefs acc := (do
  let g ← gdecl tydefs
  let tydefs := match g with | .tydef ⟨_, i⟩ => tydefs.insert i | _ => tydefs
  aux tydefs (acc.push g))
  <|> (do return acc)
