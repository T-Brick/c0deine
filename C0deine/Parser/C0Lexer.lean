import C0deine.AuxDefs
import C0deine.Parser.AuxDefs

namespace C0deine.Parser

namespace Token

inductive Num : Type
| dec (str : String)
| hex (str : String) -- str should include the 0x or 0X prefix
deriving DecidableEq, Ord

def Num.str : Num → String
| dec s => s
| hex s => s

def specialCharactersRaw := #[
    ("bang"      , "!")
  , ("tilde"     , "~")
  , ("minus"     , "-")
  , ("plus"      , "+")
  , ("star"      , "*")
  , ("div"       , "/")
  , ("mod"       , "%")
  , ("lsh"       , "<<")
  , ("rsh"       , ">>")
  , ("lt"        , "<")
  , ("gt"        , ">")
  , ("le"        , "<=")
  , ("ge"        , ">=")
  , ("eq"        , "==")
  , ("ne"        , "!=")
  , ("and"       , "&")
  , ("xor"       , "^")
  , ("or"        , "|")
  , ("andand"    , "&&")
  , ("oror"      , "||")
  , ("asn"       , "=")
  , ("plusasn"   , "+=")
  , ("minusasn"  , "-=")
  , ("starasn"   , "*=")
  , ("divasn"    , "/=")
  , ("modasn"    , "%=")
  , ("lshasn"    , "<<=")
  , ("rshasn"    , ">>=")
  , ("andasn"    , "&=")
  , ("orasn"     , "|=")
  , ("xorasn"    , "^=")
  , ("arrow"     , "->")
  , ("dot"       , ".")
  , ("minusminus", "--")
  , ("plusplus"  , "++")
  , ("lparen"    , "(")
  , ("rparen"    , ")")
  , ("lbrack"     , "[")
  , ("rbrack"     , "]")
  , ("lbrace"     , "{")
  , ("rbrace"     , "}")
  , ("comma"     , ",")
  , ("semi"      , ";")
  , ("question"  , "?")
  , ("colon"     , ":")
  ]

def keywordsRaw := #[
    "struct"
  , "typedef"
  , "if"
  , "else"
  , "while"
  , "for"
  , "continue"
  , "break"
  , "return"
  , "assert"
  , "true"
  , "false"
  , "NULL"
  , "alloc"
  , "alloc_array"
  , "int"
  , "bool"
  , "void"
  , "char"
  , "string"
  ]

/- yes, we could just write everything out by hand, but
    i wanted to show off some metaprogramming magic -james  -/
open Lean Macro in
scoped macro "genKeywordType!" : command => do
  let kwTy        := mkIdent `Keyword           -- the name of the type
  let kwToString  := mkIdent `Keyword.toString  -- the name of the toString function
  let kwArray     := mkIdent `Keyword.all
  let kwIdents := keywordsRaw.map mkIdent -- the keywords, as Lean identifiers
  let kwStrings : TSyntaxArray `term :=   -- the keywords, as Lean string literals
    keywordsRaw.map (fun kw => Syntax.mkStrLit kw)
  /- now we can just write the declarations, putting "anti-quotations"
    in as necessary. antiquotations are not well documented (april 2023).
    contact me (james gallicchio) if there are any issues/questions -/
  `(  inductive $kwTy : Type where
        $[ | $kwIdents:ident ]*
      def $kwToString : $kwTy → String
        $[ | $kwIdents:ident => $kwStrings:term ]*
      def $kwArray : Array $kwTy := #[
        $[ $kwIdents:ident ],*
      ]
  )

-- now we run the macro we just made
genKeywordType!

-- and then we do the same for special characters (now generating two functions!)
open Lean Macro in
scoped macro "genSpecialType!" : command => do
  let spTy    := mkIdent `Special
  let spName  := mkIdent `Special.name
  let spSymb  := mkIdent `Special.symbol
  let spArray := mkIdent `Special.all
  let spIdents := specialCharactersRaw.map (mkIdent ·.1)
  let spNameStrs : TSyntaxArray `term :=
    specialCharactersRaw.map (fun (name,_) => Syntax.mkStrLit name)
  let spSymbStrs : TSyntaxArray `term :=
    specialCharactersRaw.map (fun (_,sym) => Syntax.mkStrLit sym)
  `(  inductive $spTy : Type where
        $[ | $spIdents:ident ]*
      def $spName : $spTy → String
        $[ | $spIdents:ident => $spNameStrs:term ]*
      def $spSymb : $spTy → String
        $[ | $spIdents:ident => $spSymbStrs:term ]*
      def $spArray : Array $spTy := #[
        $[ $spIdents:ident ],*
      ]
  )
genSpecialType!

instance : ToString Keyword := ⟨Keyword.toString⟩
instance : ToString Special := ⟨Special.symbol⟩

deriving instance DecidableEq, Ord for Keyword
deriving instance DecidableEq, Ord for Special

end Token

inductive Token : Type
| ident (name : String)
| num (n : Token.Num)
| special (s : Token.Special)
| keyword (k : Token.Keyword)
| unknown
deriving Inhabited, DecidableEq, Ord

def Token.toString : Token → String
| ident str => s!"ident ({str})"
| num n     => n.str
| special s => s.symbol
| keyword k => k.toString
| unknown   => "<unknown>"

instance Token.instToString : ToString Token := ⟨Token.toString⟩

instance : Megaparsec.Printable.Printable Token where
  showTokens toks := toString <| toks.map (toString)

structure C0Lexer.Error where
  pos : String.Pos
deriving Inhabited, Repr

namespace C0Lexer.Error
instance : Ord Error where
  compare | ⟨p1⟩, ⟨p2⟩ => if p1 < p2 then .lt else if p1 = p2 then .eq else .gt
instance : ToString Error where
  toString e := toString e.pos
end C0Lexer.Error

open Megaparsec Parsec Common

abbrev C0Lexer := Parsec Char String C0Lexer.Error

namespace C0Lexer

def lineComment : C0Lexer Unit := do
  let _ ← string "//"
  dropMany <| void <| satisfy (· ≠ '\n')

partial def blockComment : C0Lexer Unit := do
  let _ ← string "/*"
  dropMany (
        (do let _ ← satisfy (! ['/', '*'].contains ·))
    <|> attempt (do let _ ← single '*'; notFollowedBy (single '/'))
    <|> attempt (do let _ ← single '/'; notFollowedBy (single '*'))
    <|> blockComment)
  let _ ← string "*/"

def ws : C0Lexer Unit :=
  label "ws" <|
  dropMany (
    (void <| satisfy <| List.contains
      [' ', '\n', '\t', '\r', (11 : UInt8), (12 : UInt8)])
    <|> lineComment
    <|> blockComment)

def ident : C0Lexer String :=
  label "<ident>" <| do
  let first ← label "[a-zA-Z_]" <| satisfy (fun c => c.isAlpha || c = '_')
  let rest ← takeWhileP "[a-zA-Z0-9_]" <| (fun c => c.isAlphanum || c = '_')
  return first.toString ++ rest

def num : C0Lexer Token.Num :=
  label "<number>" <| do
  (do let _ ← single '0'
      (do let _ ← single 'x' <|> single 'X'
          let s ← takeWhileP "[0-9a-fA-F]" Char.isHexDigit
          return .hex s)
      <|>
      (do return .dec "0"))
  <|>
  (do let first ← label "[1-9]" <| satisfy (fun c => '1' ≤ c && c ≤ '9')
      let rest ← takeWhileP "[0-9]" Char.isDigit
      return .dec (first.toString ++ rest))

def keyword : C0Lexer Token.Keyword :=
  Token.Keyword.all.insertionSort (·.toString.length > ·.toString.length)
  |>.toList |>.map aux |> choice
where aux (kw : Token.Keyword) :=
  label s!"'{kw}'" <| attempt do
  /- keywords should not be followed by alphanums-/
  let _ ← string kw.toString
  notFollowedBy (void <| satisfy (fun c => c.isAlphanum || c = '_'))
  return kw

-- match longest special token that can be parsed
def special : C0Lexer Token.Special :=
  Token.Special.all.insertionSort (·.symbol.length > ·.symbol.length)
  |>.toList |>.map aux |> choice
where aux (s : Token.Special) :=
  label s!"'{s.symbol}'" do
  let _ ← string s.symbol
  return s

def tokens : C0Lexer (Array (ParserState.SourcePos × Token)) := do
  ws
  let arr ← foldl #[] (fun acc => do
    let pos ← getSourcePos

    let tok ←
          (.keyword <$> keyword)
      <|> (.special <$> special)
      <|> (.num     <$> num)
      <|> (.ident   <$> ident)
    
    ws 

    return acc.push (pos,tok)
  )
  return arr


