import C0deine.IrTree.IrTree
import C0deine.Type.Typ

namespace C0deine.IrTree

open Typ

class Rewriter (α : Type) where
  rewrite_expr : (Expr → Expr) → α → α
  rewriteM_expr : [Monad m] → (Expr → m Expr) → α → m α
  rewrite_expr? : (Expr → Option Expr) → α → α :=
    fun f => rewrite_expr (fun e => (f e).getD e)
  rewriteM_expr? : [Monad m] → (Expr → m (Option Expr)) → α → m α :=
    fun f => rewriteM_expr (fun e => do return (← f e).getD e)

instance {α : Type} [Rewriter α] : Rewriter (Option α) where
  rewrite_expr := fun f => Option.map (Rewriter.rewrite_expr f)
  rewriteM_expr := fun f => Option.mapM (Rewriter.rewriteM_expr f)

instance {α : Type} [Rewriter α] : Rewriter (List α) where
  rewrite_expr := fun f => List.map (Rewriter.rewrite_expr f)
  rewriteM_expr := fun f => List.mapM (Rewriter.rewriteM_expr f)

namespace Rewriter

def Expr.rewrite (f : Expr → Expr) (e : Expr) : Expr :=
  match e with
  | .byte _ => f e
  | .const _ => f e
  | .temp _ => f e
  | .memory _ => f e
  | .binop op l r =>
    let l := ⟨l.type, rewrite f l.data⟩
    let r := ⟨r.type, rewrite f r.data⟩
    f (.binop op l r)
  | .and l r =>
    let l := ⟨l.type, rewrite f l.data⟩
    let r := ⟨r.type, rewrite f r.data⟩
    f (.and l r)
  | .or l r =>
    let l := ⟨l.type, rewrite f l.data⟩
    let r := ⟨r.type, rewrite f r.data⟩
    f (.or l r)

def Expr.rewriteM [Monad m] (f : Expr → m Expr) (e : Expr) : m Expr := do
  match e with
  | .byte _ => f e
  | .const _ => f e
  | .temp _ => f e
  | .memory _ => f e
  | .binop op l r =>
    let l := ⟨l.type, ← rewriteM f l.data⟩
    let r := ⟨r.type, ← rewriteM f r.data⟩
    f (.binop op l r)
  | .and l r =>
    let l := ⟨l.type, ← rewriteM f l.data⟩
    let r := ⟨r.type, ← rewriteM f r.data⟩
    f (.and l r)
  | .or l r =>
    let l := ⟨l.type, ← rewriteM f l.data⟩
    let r := ⟨r.type, ← rewriteM f r.data⟩
    f (.or l r)

instance : Rewriter Expr where
  rewrite_expr := Expr.rewrite
  rewriteM_expr := Expr.rewriteM
instance : Rewriter (Typed Expr) where
  rewrite_expr := fun f te => ⟨te.type, Expr.rewrite f te.data⟩
  rewriteM_expr := fun f te => do return ⟨te.type, ← Expr.rewriteM f te.data⟩

def Address.rewrite_expr (f : Expr → Expr) (addr : Address) : Address :=
  { base := Rewriter.rewrite_expr f addr.base
  , offset := addr.offset
  , index := Rewriter.rewrite_expr f addr.index
  , scale := addr.scale
  }

def Address.rewriteM_expr [Monad m]
    (f : Expr → m Expr) (addr : Address) : m Address := do
  return {
    base := ← Rewriter.rewriteM_expr f addr.base,
    offset := addr.offset,
    index := ← Rewriter.rewriteM_expr f addr.index,
    scale := addr.scale
  }
instance : Rewriter Address where
  rewrite_expr := Address.rewrite_expr
  rewriteM_expr := Address.rewriteM_expr

def Check.rewrite_expr (f : Expr → Expr) (c : Check) : Check :=
  match c with
  | .null e => .null (Rewriter.rewrite_expr f e)
  | .shift e => .shift (Rewriter.rewrite_expr f e)
  | .bounds src index =>
      .bounds (Rewriter.rewrite_expr f src) (Rewriter.rewrite_expr f index)
  | .mod l r => .mod (Rewriter.rewrite_expr f l) (Rewriter.rewrite_expr f r)

def Check.rewriteM_expr [Monad m]
    (f : Expr → m Expr) (c : Check) : m Check := do
  match c with
  | .null e => return .null (← Rewriter.rewriteM_expr f e)
  | .shift e => return .shift (← Rewriter.rewriteM_expr f e)
  | .bounds s i =>
    return .bounds (← Rewriter.rewriteM_expr f s) (← Rewriter.rewriteM_expr f i)
  | .mod l r =>
    return .mod (← Rewriter.rewriteM_expr f l) (← Rewriter.rewriteM_expr f r)
instance : Rewriter Check where
  rewrite_expr := Check.rewrite_expr
  rewriteM_expr := Check.rewriteM_expr

def Stmt.rewrite_expr (f : Expr → Expr) (s : Stmt) : Stmt :=
  match s with
  | .move dest e => .move dest (Rewriter.rewrite_expr f e)
  | .effect dest op l r =>
    .effect dest op (Rewriter.rewrite_expr f l) (Rewriter.rewrite_expr f r)
  | .call dest name args =>
    .call dest name (Rewriter.rewrite_expr f args)
  | .alloc dest size => .alloc dest (Rewriter.rewrite_expr f size)
  | .load dest addr => .load dest (Rewriter.rewrite_expr f addr)
  | .store addr src =>
    .store (Rewriter.rewrite_expr f addr) (Rewriter.rewrite_expr f src)
  | .copy dest src len =>
    .copy (Rewriter.rewrite_expr f dest) (Rewriter.rewrite_expr f src) len
  | .check c => .check (Rewriter.rewrite_expr f c)
  | .phi dest args => .phi dest args

def Stmt.rewriteM_expr [Monad m] (f : Expr → m Expr) (s : Stmt) : m Stmt :=
  match s with
  | .move dest e => return .move dest (← Rewriter.rewriteM_expr f e)
  | .effect dest op l r =>
    return .effect dest op (← Rewriter.rewriteM_expr f l) (← Rewriter.rewriteM_expr f r)
  | .call dest name args =>
    return .call dest name (← Rewriter.rewriteM_expr f args)
  | .alloc dest size => return .alloc dest (← Rewriter.rewriteM_expr f size)
  | .load dest addr => return .load dest (← Rewriter.rewriteM_expr f addr)
  | .store addr src =>
    return .store (← Rewriter.rewriteM_expr f addr) (← Rewriter.rewriteM_expr f src)
  | .copy dest src len =>
    return .copy (← Rewriter.rewriteM_expr f dest) (← Rewriter.rewriteM_expr f src) len
  | .check c => return .check (← Rewriter.rewriteM_expr f c)
  | .phi dest args => return .phi dest args

instance : Rewriter Stmt where
  rewrite_expr := Stmt.rewrite_expr
  rewriteM_expr := Stmt.rewriteM_expr

def BlockExit.rewrite_expr (f : Expr → Expr) (exit : BlockExit) : BlockExit :=
  match exit with
  | .jump lbl => .jump lbl
  | .cjump t hotpath tt ff => .cjump t hotpath tt ff
  | .return e? => .return (Rewriter.rewrite_expr f e?)
  | .error e => .error (Rewriter.rewrite_expr f e)

def BlockExit.rewriteM_expr [Monad m]
    (f : Expr → m Expr) (exit : BlockExit) : m BlockExit := do
  match exit with
  | .jump lbl => return .jump lbl
  | .cjump t hotpath tt ff => return .cjump t hotpath tt ff
  | .return e? => return .return (← Rewriter.rewriteM_expr f e?)
  | .error e => return .error (← Rewriter.rewriteM_expr f e)

instance : Rewriter BlockExit where
  rewrite_expr := BlockExit.rewrite_expr
  rewriteM_expr := BlockExit.rewriteM_expr
