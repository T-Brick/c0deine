import Std
import C0deine.Parser.Cst
import C0deine.Parser.Ast
import C0deine.Type.Typ
import C0deine.Type.Tst
import C0deine.Utils.Symbol
import C0deine.Utils.Comparison
import C0deine.Utils.Context
import C0deine.Utils.Language

/- Converts the concrete syntax tree to an abstract syntax tree
    as well as enforces a specific language level
 -/
namespace C0deine.Abstractor

def unsupported (lang : Language) (op : String) : Except String α :=
  throw s!"{lang} does not support {op}"

def Trans.type (lang : Language)
               (typ : Cst.Typ)
               : Except String (Option Ast.Typ) := do
  match typ with
  | .int => return some .int
  | .bool =>
    if lang.under .l2
    then unsupported lang "bools"
    else return some .bool
  | .void =>
    if lang.under .l3
    then unsupported lang "void function type"
    else return none
  | .tydef name =>
    if lang.under .l3
    then unsupported lang "aliased types"
    else return some (.tydef name)
  | .ptr tau =>
    if lang.under .l4
    then unsupported lang "pointer types"
    else
      let tau'Opt ← Trans.type lang tau
      return tau'Opt.map (fun tau' => .ptr tau')
  | .arr tau =>
    if lang.under .l4
    then unsupported lang "array types"
    else
      let tau'Opt ← Trans.type lang tau
      return tau'Opt.map (fun tau' => .arr tau')
  | .struct name =>
    if lang.under .l4
    then unsupported lang "structs"
    else
      return some (.struct name)

def Trans.type_nonvoid (lang : Language)
                       (typ : Cst.Typ)
                       : Except String Ast.Typ := do
  match ← Trans.type lang typ with
  | some typ' => return typ'
  | none => throw s!"void appeared where a type was expected"

def Trans.unop (lang : Language) (op : Cst.UnOp) : Except String Ast.UnOp := do
  match op with
  | .int .neg  => return .int .neg
  | .int .not  => return .int .not
  | .bool .not =>
    if lang.under .l2
    then unsupported lang "!"
    else return .bool .neg

def Trans.binop_int (lang : Language)
                    (op : Cst.BinOp.Int)
                    : Except String Ast.BinOp.Int := do
  match op with
  | .plus  => return .plus
  | .minus => return .minus
  | .times => return .times
  | .div   => return .div
  | .mod   => return .mod
  | .and   =>
    if lang.under .l2
    then unsupported lang "&"
    else return .and
  | .xor   =>
    if lang.under .l2
    then unsupported lang "^"
    else return .and
  | .or    =>
    if lang.under .l2
    then unsupported lang "|"
    else return .and
  | .lsh   =>
    if lang.under .l2
    then unsupported lang "<<"
    else return .and
  | .rsh   =>
    if lang.under .l2
    then unsupported lang ">>"
    else return .and

def Trans.binop (lang : Language)
                (op : Cst.BinOp)
                : Except String Ast.BinOp := do
  match op with
  | .int i => Trans.binop_int lang i |>.map .int
  | .cmp c =>
    if lang.under .l2
    then unsupported lang s!"{c}"
    else
      match c with
      | .lt => return .cmp .less
      | .le => return .cmp .less_equal
      | .gt => return .cmp .greater
      | .ge => return .cmp .greater_equal
      | .eq => return .cmp .equal
      | .ne => return .cmp .not_equal
  | .bool b =>
    if lang.under .l2
    then unsupported lang s!"{b}"
    else
      match b with
      | .and => return .bool .and
      | .or  => return .bool .or

def Trans.asnop (lang : Language)
                (op : Cst.AsnOp)
                : Except String Ast.AsnOp := do
  match op with
  | .eq => return .eq
  | .aseq bop => Trans.binop_int lang bop |>.map .aseq

partial def Trans.expr (lang : Language) (e : Cst.Expr) : Except String Ast.Expr := do
  match e with
  | .num n   =>
    if h : n ≤ 1 <<< 31 then
      return .num ⟨n, Nat.lt_of_le_of_lt h (by decide)⟩
    else
      throw s!"integer literal {n} is too large for a uint32"
  | .«true»  =>
    if lang.under .l2
    then unsupported lang "true"
    else return .«true»
  | .«false» =>
    if lang.under .l2
    then unsupported lang "false"
    else return .«false»
  | .null    =>
    if lang.under .l4
    then unsupported lang "NULL"
    else return .null
  | .unop op e =>
    let op' ← Trans.unop lang op
    let e' ← Trans.expr lang e
    return .unop op' e'
  | .binop op l r =>
    let op' ← Trans.binop lang op
    let l' ← Trans.expr lang l
    let r' ← Trans.expr lang r
    return .binop op' l' r'
  | .ternop cond tt ff =>
    if lang.under .l2
    then unsupported lang "ternary operators"
    else
      let cond' ← Trans.expr lang cond
      let tt' ← Trans.expr lang tt
      let ff' ← Trans.expr lang ff
      return .ternop cond' tt' ff'
  | .app f args =>
    if lang.under .l3
    then unsupported lang "function application"
    else
      let args' ← args.mapM (Trans.expr lang)
      return .app f args'
  | .alloc ty =>
    if lang.under .l4
    then unsupported lang "memory allocation"
    else
      let ty' ← Trans.type_nonvoid lang ty
      return .alloc ty'
  | .alloc_array ty e =>
    if lang.under .l4
    then unsupported lang "array allocation"
    else
      let ty' ← Trans.type_nonvoid lang ty
      let e' ← Trans.expr lang e
      return .alloc_array ty' e'
  | .var name => return .var name
  | .dot e field =>
    if lang.under .l4
    then unsupported lang "struct dot accessor"
    else
      let e' ← Trans.expr lang e
      return .dot e' field
  | .arrow e field =>
    if lang.under .l4
    then unsupported lang "struct arrow accessor"
    else
      let e' ← Trans.expr lang e
      return .arrow e' field
  | .deref e =>
    if lang.under .l4
    then unsupported lang "dereferencing"
    else
      let e' ← Trans.expr lang e
      return .deref e'
  | .index e indx =>
    if lang.under .l4
    then unsupported lang "array indexing"
    else
      let e' ← Trans.expr lang e
      let indx' ← Trans.expr lang indx
      return .index e' indx'

def Trans.lvalue (lang : Language)
                 (lv : Cst.LValue)
                 : Except String Ast.LValue := do
  match lv with
  | .var name => return .var name
  | .dot lv field =>
    if lang.under .l4
    then unsupported lang "struct dot accessor"
    else
      let lv' ← Trans.lvalue lang lv
      return .dot lv' field
  | .arrow lv field =>
    if lang.under .l4
    then unsupported lang "struct arrow accessor"
    else
      let lv' ← Trans.lvalue lang lv
      return .arrow lv' field
  | .deref lv =>
    if lang.under .l4
    then unsupported lang "dereferencing"
    else
      let lv' ← Trans.lvalue lang lv
      return .deref lv'
  | .index lv indx =>
    if lang.under .l4
    then unsupported lang "array indexing"
    else
      let lv' ← Trans.lvalue lang lv
      let indx' ← Trans.expr lang indx
      return .index lv' indx'


mutual
partial def Trans.stmts (lang : Language)
                (stmts : List Cst.Stmt)
                : Except String (List Ast.Stmt) := do
  match stmts with
  | [] => return []
  | .simp simp :: rest => Trans.simp lang simp rest
  | .ctrl ctrl :: rest => Trans.control lang ctrl rest
  | .block blk :: rest =>
    let blk' ← Trans.stmts lang blk
    let rest' ← Trans.stmts lang rest
    return blk'.append rest'

partial def Trans.simp (lang : Language)
               (simp : Cst.Simp)
               (rest : List Cst.Stmt)
               : Except String (List Ast.Stmt) := do
  match simp with
  | .assn lv op v =>
    let lv' ← Trans.lvalue lang lv
    let op' ← Trans.asnop lang op
    let v' ← Trans.expr lang v
    let rest' ← Trans.stmts lang rest
    return .assn lv' op' v' :: rest'
  | .post lv op =>
    if lang.under .l2
    then unsupported lang "post operators"
    else
      let lv' ← Trans.lvalue lang lv
      let rest' ← Trans.stmts lang rest
      match op with
      | .incr => return .assn lv' (.aseq .plus) (.num 1) :: rest'
      | .decr => return .assn lv' (.aseq .minus) (.num 1) :: rest'
  | .decl type name init =>
    let type' ← Trans.type_nonvoid lang type
    let init' ← init.mapM (Trans.expr lang)
    let rest' ← Trans.stmts lang rest
    return .decl type' name init' rest' :: []
  | .exp e =>
    if lang.under .l2
    then unsupported lang "expression statements"
    else
      let e' ← Trans.expr lang e
      let rest' ← Trans.stmts lang rest
      return .exp e' :: rest'

partial def Trans.control (lang : Language)
                  (ctrl : Cst.Control)
                  (rest : List Cst.Stmt)
                  : Except String (List Ast.Stmt) := do
  match ctrl with
  | .ite cond tt ff =>
    if lang.under .l2
    then unsupported lang "if-else statements"
    else
      let cond' ← Trans.expr lang cond
      let tt' ← Trans.stmts lang [tt]
      let ff' ← Trans.stmts lang [ff]
      let rest' ← Trans.stmts lang rest
      return (.ite cond' tt' ff') :: rest'
  | .while cond body =>
    if lang.under .l2
    then unsupported lang "while loops"
    else
      let cond' ← Trans.expr lang cond
      let body' ← Trans.stmts lang [body]
      let rest' ← Trans.stmts lang rest
      return (.while cond' body') :: rest'
  | .«for» initOpt cond stepOpt body =>
    if lang.under .l2
    then unsupported lang "for loops"
    else
      match stepOpt with
      | some (.decl _ _ _) => throw s!"For loop steps cannot have declarations"
      | some step =>
        let bodyStep := .block [body, .simp step]
        let whileStmt := .ctrl (.while cond bodyStep)
        match initOpt with
        | some init =>
          let initBody' ← Trans.simp lang init [whileStmt]
          let rest' ← Trans.stmts lang rest
          return initBody'.append rest'
        | none => Trans.stmts lang (whileStmt :: rest)
      | none =>
        let whileStmt := .ctrl (.while cond body)
        match initOpt with
        | some init =>
          let initBody' ← Trans.simp lang init [whileStmt]
          let rest' ← Trans.stmts lang rest
          return initBody'.append rest'
        | none => Trans.stmts lang (whileStmt :: rest)
  | .«return» (some e) =>
    let e' ← Trans.expr lang e
    let rest' ← Trans.stmts lang rest
    return .«return» (some e') :: rest'
  | .«return» (none) =>
    if lang.under .l3
    then unsupported lang "void return statements"
    else
      let rest' ← Trans.stmts lang rest
      return .«return» none :: rest'
  | .assert e =>
    if lang.under .l3
    then unsupported lang "assert statements"
    else
      let e' ← Trans.expr lang e
      let rest' ← Trans.stmts lang rest
      return .assert e' :: rest'
end

def Trans.param (lang : Language)
                (p : Cst.Param)
                : Except String Ast.Param := do
  if lang.under .l3
  then unsupported lang "functions with parameters"
  else return ⟨← Trans.type_nonvoid lang p.type, p.name⟩

def Trans.field (lang : Language)
                (f : Cst.Field)
                : Except String Ast.Field := do
  return ⟨← Trans.type_nonvoid lang f.type, f.name⟩

def Trans.gdecl (lang : Language)
                (gdec : Cst.GDecl)
                : Except String (Ast.GDecl) := do
  match gdec with
  | .fdecl f =>
    if lang.under .l3
    then unsupported lang "function declarations"
    else
      let type' ← Trans.type lang f.type
      let params' ← f.params.mapM (Trans.param lang)
      return .fdecl ⟨type', f.name, params'⟩
  | .fdef f =>
    if f.name.name != "main" && lang.under .l3
    then unsupported lang "functions that aren't main"
    else
      let type' ← Trans.type lang f.type
      let params' ← f.params.mapM (Trans.param lang)
      let body' ← Trans.stmts lang [f.body]
      return .fdef ⟨type', f.name, params', body'⟩
  | .tydef t =>
    if lang.under .l3
    then unsupported lang "typdefs"
    else return .tydef ⟨← Trans.type_nonvoid lang t.type, t.name⟩
  | .sdecl s =>
    if lang.under .l4
    then unsupported lang "struct declarations"
    else return .sdecl ⟨s.name⟩
  | .sdef  s =>
    if lang.under .l4
    then unsupported lang "struct definitions"
    else return .sdef ⟨s.name, ← s.fields.mapM (Trans.field lang)⟩

def abstract (lang : Language) (prog : Cst.Prog) : Except String Ast.Prog :=
  prog.mapM (Trans.gdecl lang)
