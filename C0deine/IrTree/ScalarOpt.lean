import C0deine.IrTree.IrTree
import C0deine.IrTree.Rewriter

namespace C0deine.IrTree.ScalarOpt

inductive Value
| byte : UInt8 → Value
| const : _root_.Int32 → Value
| copy : SizedTemp → Value

def Value.toExpr : Value → Expr
| .byte b => .byte b
| .const n => .const n
| .copy t => .temp t

structure Context where
  mapping : Std.HashMap Temp Value := Std.HashMap.emptyWithCapacity
deriving Inhabited

def get_value (t : Temp) : StateM Context (Option Value) := fun s =>
  (s.mapping.get? t, s)
def set_value (t : Temp) (v : Value) : StateM Context Unit := fun s =>
  ((), { s with mapping := s.mapping.insert t v})

def expr_folder (e : Expr) : StateM Context Expr := do
  match e with
  | .temp t =>
    match ← get_value t.data with
    | .some v => return v.toExpr
    | .none => return e

  | .binop op l r =>
    match op, l.data, r.data with
    | .add, .byte lv, .byte rv => return .byte (lv + rv)
    | .sub, .byte lv, .byte rv => return .byte (lv - rv)
    | .mul, .byte lv, .byte rv => return .byte (lv * rv)
    | .and, .byte lv, .byte rv => return .byte (lv &&& rv)
    | .or , .byte lv, .byte rv => return .byte (lv ||| rv)
    | .xor, .byte lv, .byte rv => return .byte (lv ^^^ rv)
    | .comp .less,          .byte lv, .byte rv => return .byte (if lv < rv then 1 else 0)
    | .comp .greater,       .byte lv, .byte rv => return .byte (if lv > rv then 1 else 0)
    | .comp .equal,         .byte lv, .byte rv => return .byte (if lv = rv then 1 else 0)
    | .comp .not_equal,     .byte lv, .byte rv => return .byte (if lv != rv then 1 else 0)
    | .comp .less_equal,    .byte lv, .byte rv => return .byte (if lv <= rv then 1 else 0)
    | .comp .greater_equal, .byte lv, .byte rv => return .byte (if lv >= rv then 1 else 0)

    | .add, .const lv, .const rv => return .const (lv + rv)
    | .sub, .const lv, .const rv => return .const (lv - rv)
    | .mul, .const lv, .const rv => return .const (lv * rv)
    | .and, .const lv, .const rv => return .const (lv &&& rv)
    | .or , .const lv, .const rv => return .const (lv ||| rv)
    | .xor, .const lv, .const rv => return .const (lv ^^^ rv)
    | .comp .less,          .const lv, .const rv => return .byte (if lv < rv then 1 else 0)
    | .comp .greater,       .const lv, .const rv => return .byte (if lv > rv then 1 else 0)
    | .comp .equal,         .const lv, .const rv => return .byte (if lv = rv then 1 else 0)
    | .comp .not_equal,     .const lv, .const rv => return .byte (if lv != rv then 1 else 0)
    | .comp .less_equal,    .const lv, .const rv => return .byte (if lv <= rv then 1 else 0)
    | .comp .greater_equal, .const lv, .const rv => return .byte (if lv >= rv then 1 else 0)

    | .add, l, .const rv
    | .sub, l, .const rv
    | .or , l, .const rv
    | .xor, l, .const rv => if rv = 0 then return l
    | .mul, l, .const rv => if rv = 1 then return l
    | .and, _, .const rv => if rv = 0 then return .const 0

    | .add, .const lv, r
    | .sub, .const lv, r
    | .or , .const lv, r
    | .xor, .const lv, r => if lv = 0 then return r
    | .mul, .const lv, r => if lv = 1 then return r
    | .and, .const lv, _ => if lv = 0 then return .const 0

    | _, _, _ => return e

  | .and l r =>
    match l.data, r.data with
    | _, .byte 0
    | .byte 0, _
    | .const 0, _
    | _, .const 0 => return .byte 0

    | .byte lv, .byte rv => return .byte (if lv ≠ 0 && rv ≠ 0 then 1 else 0)
    | .const lv, .const rv => return .byte (if lv ≠ 0 && rv ≠ 0 then 1 else 0)

    | .byte _, r
    | .const _, r => return r
    | l, .byte _
    | l, .const _ => return l

    | _, _ => return e

  | .or l r =>
    match l.data, r.data with
    | .byte lv, .byte rv => return .byte (if lv ≠ 0 || rv ≠ 0 then 1 else 0)
    | .const lv, .const rv => return .byte (if lv ≠ 0 || rv ≠ 0 then 1 else 0)

    | .byte 0, r
    | .const 0, r => return r
    | l, .byte 0
    | l, .const 0 => return l

    | _, .byte _
    | .byte _, _
    | .const _, _
    | _, .const _ => return .byte 1

    | _, _ => return e

  | e => return e
  return e

def stmt_folder (s : Stmt) : StateM Context (Option Stmt) := do
  match s with
  | .move dest e =>
    match e.data with
    | .byte b =>
      let _ ← set_value dest.data (.byte b)
      return s
    | .const n =>
      let _ ← set_value dest.data (.const n)
      return s
    | .temp t =>
      let _ ← set_value dest.data (.copy t)
      return s
    | _ => return s

  | .effect dest op l r =>
    match op, l.data, r.data with
    | .div, .const lv, .const rv =>
      if rv ≠ 0 then
        return .some <| .move dest ⟨.prim .int, .const (lv / rv)⟩
    | .div, _, .const 1 => return .some <| .move dest l
    | .div, .const 0, _ => return .some <| .move dest ⟨.prim .int, .const 0⟩

    | .mod, .const lv, .const rv =>
      if rv ≠ 0 then
        return .some <| .move dest ⟨.prim .int, .const (lv % rv)⟩
    | .mod, _, .const 1 => return .some <| .move dest l
    | .mod, .const 0, _ => return .some <| .move dest ⟨.prim .int, .const 0⟩

    | .lsh, .const lv, .const rv =>
      if 0 ≤ rv && rv < 32 then
        return .some <| .move dest ⟨.prim .int, .const (lv <<< rv)⟩
    | .lsh, .const 0, _ => return .some <| .move dest ⟨.prim .int, .const 0⟩
    | .lsh, _, .const 0 => return .some <| .move dest l

    | .rsh, .const lv, .const rv =>
      if 0 ≤ rv && rv < 32 then
        return .some <| .move dest ⟨.prim .int, .const (lv >>> rv)⟩
    | .rsh, .const 0, _ => return .some <| .move dest ⟨.prim .int, .const 0⟩
    | .rsh, _, .const 0 => return .some <| .move dest l

    | _, _, _ => return s

  | .check (.null e) =>
    match e.data with
    | .byte n => if n != 0 then return none
    | .const n => if n != 0 then return none
    | _ => return s

  | .check (.shift e) =>
    match e.data with
    | .byte n => if 0 ≤ n && n < 8 then return none
    | .const n => if 0 ≤ n && n < 32 then return none
    | _ => return s

  | _ => return s
  return s

def run (p : Prog) : Prog := (
    StmtRewriter.rewriteM_stmt (fun s => do
      stmt_folder (← ExprRewriter.rewriteM_expr expr_folder s)
    ) p
  ) ({} : Context) |>.fst
