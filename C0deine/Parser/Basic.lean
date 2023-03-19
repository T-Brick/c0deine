import Std
import Parser

import C0deine.Utils.Context
import C0deine.Parser.Cst
import C0deine.AuxDefs

open Parser

namespace C0deine.Parser


abbrev C0Parser := SimpleParserT Substring Char (ExceptT (Parser.Error.Simple Substring Char) Context)

namespace C0Parser

/-- `notFollowedBy p` succeeds only if `p` fails -/
@[inline] def _root_.Parser.notFollowedBy' {ε σ α β}
  [Parser.Stream σ α] [Parser.Error ε σ α] {m} [Monad m] [MonadExceptOf ε m]
 (p : ParserT ε σ α m β) : ParserT ε σ α m Unit := do
  try
    let _ ← lookAhead p
  catch _ =>
    return
  throwUnexpected

def noBacktrackOr (p1 p2 : C0Parser α) := do
  let oldPos ← getPosition
  try p1
  catch e =>
    if (← getPosition) ≠ oldPos then
      throw e
    else
      p2

notation p1 " </> " p2 => noBacktrackOr p1 p2

open Cst

instance : MonadLiftT Context C0Parser :=
  show MonadLiftT _ (StateT _ _) from inferInstance
instance : Inhabited (C0Parser α) := ⟨throwUnexpected⟩

private def char (c : Char) : C0Parser Unit := do let _ ← Char.char c
private def chars (s : String) : C0Parser Unit := do let _ ← Char.chars s

def intmin : UInt32 := 0x80000000
example : intmin.val = 1 <<< 31 := rfl

def num : C0Parser UInt32 := do
  dec </> hex </> (do let _ ← chars "-2147483648"; return intmin)
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
    let _ ← (Char.char 'x' </> Char.char 'X')
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
    </> (do char '*'; notFollowedBy (do char '/'))
    </> (do char '/'; notFollowedBy (do char '*'))
    </> blockComment)
  chars "*/"

def ws : C0Parser Unit :=
  withErrorMessage "ws" <|
  dropMany (
    (do let _ ← tokenFilter (· ∈ [' ', '\n', '\t', '\r', '\u0011', '\u0012']))
    </> lineComment
    </> blockComment)

@[inline] def keyword (s : String) : C0Parser Unit := withBacktracking do
  /- keywords should not be followed by alphanums-/
  chars s
  notFollowedBy (tokenFilter (·.isAlphanum))

def kw_struct       := keyword "struct"
def kw_typedef      := keyword "typedef"
def kw_if           := keyword "if"
def kw_else         := keyword "else"
def kw_while        := keyword "while"
def kw_for          := keyword "for"
def kw_continue     := keyword "continue"
def kw_break        := keyword "break"
def kw_return       := keyword "return"
def kw_assert       := keyword "assert"
def kw_true         := keyword "true"
def kw_false        := keyword "false"
def kw_NULL         := keyword "NULL"
def kw_alloc        := keyword "alloc"
def kw_alloc_array  := keyword "alloc_array"
def kw_int          := keyword "int"
def kw_bool         := keyword "bool"
def kw_void         := keyword "void"
def kw_char         := keyword "char"
def kw_string       := keyword "string"

def anyKeyword : C0Parser Unit :=
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

def rawIdent : C0Parser Ident := do
  notFollowedBy' anyToken --anyKeyword
  let c ← tokenFilter (fun c => c.isAlpha || c = '_')
  let str ← foldl String.push (return c.toString) (tokenFilter (fun c => c.isAlphanum || c = '_'))
  return ← liftM <| Symbol.symbol str

def typeIdent : C0Parser Ident :=
  withErrorMessage "<type-ident>" do
  let id ← rawIdent
  if tydefs.contains id then
    return id
  else
    throwUnexpected

def ident : C0Parser Ident :=
  withErrorMessage "<ident>" do
  let id ← rawIdent
  if tydefs.contains id then
    throwUnexpected
  else
    return id


mutual
def simpleTyp : C0Parser Typ :=
      (do kw_int ; return Typ.int)
  </> (do kw_bool; return Typ.bool)
  </> (do kw_void; return Typ.void)
  </> (do let name ← ident tydefs; return Typ.tydef name)
  </> (do kw_struct; ws; let name ← ident tydefs; return Typ.struct name)

def typ : C0Parser Typ :=
  withErrorMessage "<type>" do
  -- parse a simple type
  let t ← simpleTyp
  -- parse as many * and [] as we can
  foldl (fun t (f : Typ → Typ) => f t)
    (return t)
    (do
      ws
      (do char '*'; return Typ.ptr)
      </> (do char '['; ws; char ']'; return Typ.arr) )
end

def unop.int : C0Parser UnOp.Int :=
  (do char '-'; notFollowedBy (char '-'); notFollowedBy (char '>'); return .neg)
  </> (do char '~'; return .not)

def unop.bool : C0Parser UnOp.Bool :=
  (do char '!'; return .not)

def unop : C0Parser UnOp :=
    (do let op ← unop.int; return .int op)
</> (do let op ← unop.bool; return .bool op)

def binop.int.prec_11 : C0Parser BinOp.Int :=
     (do char '*'; return .times)
</> (do char '/'; return .div)
</> (do char '%'; return .mod)

def binop.int.prec_10 : C0Parser BinOp.Int :=
    (do char '+'; return .plus)
</> (do char '-'; notFollowedBy (char '-'); return .minus)

def binop.int.prec_9 : C0Parser BinOp.Int :=
    (do chars "<<"; return .lsh)
</> (do chars ">>"; return .rsh)

def binop.cmp.prec_8 : C0Parser BinOp.Cmp :=
    (do char '<'; return .lt)
</> (do chars "<="; return .le)
</> (do char '>'; return .gt)
</> (do chars ">="; return .ge)

def binop.cmp.prec_7 : C0Parser BinOp.Cmp :=
    (do chars "=="; return .eq)
</> (do chars "!="; return .ne)

def binop.int.prec_6 : C0Parser BinOp.Int :=
  (do char '&'; return .and)

def binop.int.prec_5 : C0Parser BinOp.Int :=
  (do char '^'; return .xor)

def binop.int.prec_4 : C0Parser BinOp.Int :=
  (do char '|'; return .or)

def binop.bool.prec_3 : C0Parser BinOp.Bool :=
  (do chars "&&"; return .and)

def binop.bool.prec_2 : C0Parser BinOp.Bool :=
  (do chars "||"; return .or)

def binop.int : C0Parser BinOp.Int :=
  binop.int.prec_11 </> binop.int.prec_10 </> binop.int.prec_9
  </> binop.int.prec_6 </> binop.int.prec_5 </> binop.int.prec_4

def asnop : C0Parser AsnOp :=
    (do char '='; return .eq)
</> (do let op ← binop.int; char '='; return .aseq op)

def postop : C0Parser PostOp :=
    (do chars "++"; return .incr)
</> (do chars "--"; return .decr)

mutual
partial def lvalue : C0Parser LValue :=
  foldl (fun x (f : LValue → LValue) => f x)
    (do let name ← ident tydefs; return .var name)
    (do
      ws
      (do
        char '.'; ws
        let field ← ident tydefs
        return (.dot · field))
      </> (do
        chars "->"; ws
        let field ← ident tydefs
        return (.arrow · field))
      </> (do
        char '*'; ws
        return (.deref ·))
      </> (do
        char '['; ws; let index ← expr; char ']'
        return (.index · index))
    )

partial def expr.prec_13.left : C0Parser Expr :=
    (do let v ← num; return .num v)
</> (do kw_true; return .«true»)
</> (do kw_false; return .«false»)
</> (do kw_NULL; return .null)
</> (do kw_alloc; ws; char '('; ws
        let ty ← typ tydefs
        ws; char ')'
        return .alloc ty)
</> (do kw_alloc_array; ws; char '('; ws
        let ty ← typ tydefs
        ws; char ','; ws
        let e ← expr
        ws; char ')'
        return .alloc_array ty e)
</> (do let name ← ident tydefs
        (do ws; char '('; ws
            let args ← foldl (Array.push)
              (do let e ← expr; return #[e])
              (do ws; char ','; ws; expr)
            char ')'
            return .app name args.toList)
        </>
        (return .var name))
</> (do char '('; let e ← expr; char ')'; return e)

partial def expr.prec_13 : C0Parser Expr :=
  foldl (fun x (f : Expr → Expr) => f x) expr.prec_13.left
    (   (do ws; char '.'  ; ws; let f ← ident tydefs; return (.dot · f))
    </> (do ws; chars "->"; ws; let f ← ident tydefs; return (.arrow · f))
    </> (do ws; char '['  ; ws; let e ← expr; return (.index · e)))

partial def expr.prec_12 : C0Parser Expr :=
    (do let op ← unop; ws; return .unop op (← expr.prec_12))
</> (do char '*'; ws; return .deref (← expr.prec_12))
</> expr.prec_13

partial def expr.prec_11 : C0Parser Expr :=
  foldl (fun x (f : Expr → Expr) => f x) expr.prec_12
    (do ws; let op ← binop.int.prec_11; ws; let rhs ← expr.prec_12; return (.binop (.int op) · rhs))

partial def expr.prec_10 : C0Parser Expr :=
  foldl (fun x (f : Expr → Expr) => f x) expr.prec_11
    (do ws; let op ← binop.int.prec_10; ws; let rhs ← expr.prec_11; return (.binop (.int op) · rhs))

partial def expr.prec_9 : C0Parser Expr :=
  foldl (fun x (f : Expr → Expr) => f x) expr.prec_10
    (do ws; let op ← binop.int.prec_9; ws; let rhs ← expr.prec_10; return (.binop (.int op) · rhs))

partial def expr.prec_8 : C0Parser Expr :=
  foldl (fun x (f : Expr → Expr) => f x) expr.prec_9
    (do ws; let op ← binop.cmp.prec_8; ws; let rhs ← expr.prec_9; return (.binop (.cmp op) · rhs))

partial def expr.prec_7 : C0Parser Expr :=
  foldl (fun x (f : Expr → Expr) => f x) expr.prec_8
    (do ws; let op ← binop.cmp.prec_7; ws; let rhs ← expr.prec_8; return (.binop (.cmp op) · rhs))

partial def expr.prec_6 : C0Parser Expr :=
  foldl (fun x (f : Expr → Expr) => f x) expr.prec_7
    (do ws; let op ← binop.int.prec_6; ws; let rhs ← expr.prec_7; return (.binop (.int op) · rhs))

partial def expr.prec_5 : C0Parser Expr :=
  foldl (fun x (f : Expr → Expr) => f x) expr.prec_6
    (do ws; let op ← binop.int.prec_5; ws; let rhs ← expr.prec_6; return (.binop (.int op) · rhs))

partial def expr.prec_4 : C0Parser Expr :=
  foldl (fun x (f : Expr → Expr) => f x) expr.prec_5
    (do ws; let op ← binop.int.prec_4; ws; let rhs ← expr.prec_5; return (.binop (.int op) · rhs))

partial def expr.prec_3 : C0Parser Expr :=
  foldl (fun x (f : Expr → Expr) => f x) expr.prec_4
    (do ws; let op ← binop.bool.prec_3; ws; let rhs ← expr.prec_4; return (.binop (.bool op) · rhs))

partial def expr.prec_2 : C0Parser Expr :=
  foldl (fun x (f : Expr → Expr) => f x) expr.prec_3
    (do ws; let op ← binop.bool.prec_2; ws; let rhs ← expr.prec_3; return (.binop (.bool op) · rhs))

partial def expr.prec_1 : C0Parser Expr := do
  let lhs ← expr.prec_2
  (do ws; char '?'; ws; let tt ← expr.prec_1; ws; char ':'; ws; let ff ← expr.prec_1;
      return .ternop lhs tt ff)
  </> (do return lhs)

partial def expr : C0Parser Expr := expr.prec_1
end

mutual
partial def control : C0Parser Control :=
    (do kw_if; ws; char '('; ws; let cond ← expr tydefs; ws; char ')'; ws
        let tt ← stmt
        let ff ← option? (do ws; kw_else; stmt)
        return Control.ite cond tt (ff.getD (.block [])))
</> (do kw_while; ws; char '('; ws; let cond ← expr tydefs; ws; char ')'; ws
        let body ← stmt
        return Control.«while» cond body)
</> (do kw_for; ws; char '('; ws;
        let init ← simp; ws; char ';'; ws; let cond ← expr tydefs; ws; char ';'; ws; let step ← option? simp; ws; char ')'; ws
        let body ← stmt
        return Control.«for» init cond step body)
</> (do kw_return; ws; let e ← option? (expr tydefs); ws; char ';'
        return Control.«return» e)
</> (do kw_assert; ws; let e ← expr tydefs; ws; char ';'
        return Control.assert e)

partial def simp : C0Parser Simp :=
    (do let type ← typ tydefs; ws
        let name ← ident tydefs; ws;
        let init ← option? (do char '='; ws; expr tydefs)
        return .decl type name init)
</> (do let lv ← lvalue tydefs; ws
        let op ← asnop; ws
        let v ← expr tydefs
        return .assn lv op v)
</> (do let lv ← lvalue tydefs; ws
        let op ← postop
        return .post lv op)
</> (do let e ← expr tydefs; return .exp e)

partial def block : C0Parser Stmt :=
    (do char '{'; ws; char '}'
        return .block [])
</> (do char '{'; ws
        let body ← sepBy ws stmt
        ws; char '}'
        return .block body.toList)

partial def stmt : C0Parser Stmt :=
    (do let s ← simp; ws; char ';'; return .simp s)
</> (do return .ctrl (←control))
</> block
end

def field : C0Parser Field := do
  let type ← typ tydefs
  ws
  let name ← ident tydefs
  char ';'
  return ⟨type, name⟩

def sdef : C0Parser SDef :=
  withErrorMessage "<struct-def>" do
  kw_struct; ws
  let name ← ident tydefs; ws
  char '{'; ws
  let fields ← sepBy ws (field tydefs)
  ws; char '}'; char ';'
  return ⟨name, fields.toList⟩

def sdecl : C0Parser SDecl :=
  withErrorMessage "<struct-decl>" do
  kw_struct; ws
  let name ← ident tydefs; ws
  char ';'
  return ⟨name⟩

def tydef : C0Parser TyDef :=
  withErrorMessage "<type-def>" do
  kw_typedef; ws
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

def fdecl : C0Parser FDecl :=
  withErrorMessage "<func-decl>" do
  let sig ← signature tydefs
  ws; char ';'
  return sig

def fdef : C0Parser FDef :=
  withErrorMessage "<func-def>" do
  let sig ← signature tydefs
  ws
  let body ← block tydefs
  return {sig with body}

def gdecl : C0Parser GDecl :=
    (do return .fdecl (← fdecl tydefs)) 
</> (do return .tydef (← tydef tydefs))
</> (do return .sdecl (← sdecl tydefs))
</> (do return .sdef  (← sdef  tydefs)) 
</> (do return .fdef  (← fdef  tydefs))

partial def prog : C0Parser Prog :=
  withErrorMessage "<prog>" do
  ws
  let gdecls ← aux (Std.RBSet.empty) #[]
  return gdecls.toList
where aux tydefs acc :=
  (do Parser.endOfInput; return acc)
  </> (do
    let g ← gdecl tydefs
    ws
    let tydefs := match g with | .tydef ⟨_, i⟩ => tydefs.insert i | _ => tydefs
    aux tydefs (acc.push g))
