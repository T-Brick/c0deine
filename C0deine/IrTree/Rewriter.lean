import C0deine.IrTree.IrTree
import C0deine.Type.Typ

namespace C0deine.IrTree

open Typ

class ExprRewriter (α : Type) where
  rewrite_expr : (Expr → Expr) → α → α
  rewriteM_expr : [Monad m] → (Expr → m Expr) → α → m α
  rewrite_expr? : (Expr → Option Expr) → α → α :=
    fun f => rewrite_expr (fun e => (f e).getD e)
  rewriteM_expr? : [Monad m] → (Expr → m (Option Expr)) → α → m α :=
    fun f => rewriteM_expr (fun e => do return (← f e).getD e)

instance {α : Type} [ExprRewriter α] : ExprRewriter (Option α) where
  rewrite_expr := fun f => Option.map (ExprRewriter.rewrite_expr f)
  rewriteM_expr := fun f => Option.mapM (ExprRewriter.rewriteM_expr f)

instance {α : Type} [ExprRewriter α] : ExprRewriter (List α) where
  rewrite_expr := fun f => List.map (ExprRewriter.rewrite_expr f)
  rewriteM_expr := fun f => List.mapM (ExprRewriter.rewriteM_expr f)

class StmtRewriter (α : Type) where
  rewrite_stmt : (Stmt → Option Stmt) → α → α
  rewriteM_stmt : [Monad m] → (Stmt → m (Option Stmt)) → α → m α

instance {α : Type} [StmtRewriter α] : StmtRewriter (Option α) where
  rewrite_stmt := fun f => Option.map (StmtRewriter.rewrite_stmt f)
  rewriteM_stmt := fun f => Option.mapM (StmtRewriter.rewriteM_stmt f)

instance {α : Type} [StmtRewriter α] : StmtRewriter (List α) where
  rewrite_stmt := fun f => List.map (StmtRewriter.rewrite_stmt f)
  rewriteM_stmt := fun f => List.mapM (StmtRewriter.rewriteM_stmt f)

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

instance : ExprRewriter Expr where
  rewrite_expr := Expr.rewrite
  rewriteM_expr := Expr.rewriteM
instance : ExprRewriter (Typed Expr) where
  rewrite_expr := fun f te => ⟨te.type, Expr.rewrite f te.data⟩
  rewriteM_expr := fun f te => do return ⟨te.type, ← Expr.rewriteM f te.data⟩

def Address.rewrite_expr (f : Expr → Expr) (addr : Address) : Address :=
  { base := ExprRewriter.rewrite_expr f addr.base
  , offset := addr.offset
  , index := ExprRewriter.rewrite_expr f addr.index
  , scale := addr.scale
  }

def Address.rewriteM_expr [Monad m]
    (f : Expr → m Expr) (addr : Address) : m Address := do
  return {
    base := ← ExprRewriter.rewriteM_expr f addr.base,
    offset := addr.offset,
    index := ← ExprRewriter.rewriteM_expr f addr.index,
    scale := addr.scale
  }
instance : ExprRewriter Address where
  rewrite_expr := Address.rewrite_expr
  rewriteM_expr := Address.rewriteM_expr

def Check.rewrite_expr (f : Expr → Expr) (c : Check) : Check :=
  match c with
  | .null e => .null (ExprRewriter.rewrite_expr f e)
  | .shift e => .shift (ExprRewriter.rewrite_expr f e)
  | .bounds src index =>
      .bounds (ExprRewriter.rewrite_expr f src) (ExprRewriter.rewrite_expr f index)
  | .mod l r => .mod (ExprRewriter.rewrite_expr f l) (ExprRewriter.rewrite_expr f r)

def Check.rewriteM_expr [Monad m]
    (f : Expr → m Expr) (c : Check) : m Check := do
  match c with
  | .null e => return .null (← ExprRewriter.rewriteM_expr f e)
  | .shift e => return .shift (← ExprRewriter.rewriteM_expr f e)
  | .bounds s i =>
    return .bounds (← ExprRewriter.rewriteM_expr f s) (← ExprRewriter.rewriteM_expr f i)
  | .mod l r =>
    return .mod (← ExprRewriter.rewriteM_expr f l) (← ExprRewriter.rewriteM_expr f r)
instance : ExprRewriter Check where
  rewrite_expr := Check.rewrite_expr
  rewriteM_expr := Check.rewriteM_expr

def Stmt.rewrite_expr (f : Expr → Expr) (s : Stmt) : Stmt :=
  match s with
  | .move dest e => .move dest (ExprRewriter.rewrite_expr f e)
  | .effect dest op l r =>
    .effect dest op (ExprRewriter.rewrite_expr f l) (ExprRewriter.rewrite_expr f r)
  | .call dest name args =>
    .call dest name (ExprRewriter.rewrite_expr f args)
  | .alloc dest size => .alloc dest (ExprRewriter.rewrite_expr f size)
  | .load dest addr => .load dest (ExprRewriter.rewrite_expr f addr)
  | .store addr src =>
    .store (ExprRewriter.rewrite_expr f addr) (ExprRewriter.rewrite_expr f src)
  | .copy dest src len =>
    .copy (ExprRewriter.rewrite_expr f dest) (ExprRewriter.rewrite_expr f src) len
  | .check c => .check (ExprRewriter.rewrite_expr f c)
  | .phi dest args => .phi dest args

def Stmt.rewriteM_expr [Monad m] (f : Expr → m Expr) (s : Stmt) : m Stmt :=
  match s with
  | .move dest e => return .move dest (← ExprRewriter.rewriteM_expr f e)
  | .effect dest op l r =>
    return .effect dest op (← ExprRewriter.rewriteM_expr f l) (← ExprRewriter.rewriteM_expr f r)
  | .call dest name args =>
    return .call dest name (← ExprRewriter.rewriteM_expr f args)
  | .alloc dest size => return .alloc dest (← ExprRewriter.rewriteM_expr f size)
  | .load dest addr => return .load dest (← ExprRewriter.rewriteM_expr f addr)
  | .store addr src =>
    return .store (← ExprRewriter.rewriteM_expr f addr) (← ExprRewriter.rewriteM_expr f src)
  | .copy dest src len =>
    return .copy (← ExprRewriter.rewriteM_expr f dest) (← ExprRewriter.rewriteM_expr f src) len
  | .check c => return .check (← ExprRewriter.rewriteM_expr f c)
  | .phi dest args => return .phi dest args

instance : ExprRewriter Stmt where
  rewrite_expr := Stmt.rewrite_expr
  rewriteM_expr := Stmt.rewriteM_expr

def BlockExit.rewrite_expr (f : Expr → Expr) (exit : BlockExit) : BlockExit :=
  match exit with
  | .jump lbl => .jump lbl
  | .cjump t hotpath tt ff => .cjump t hotpath tt ff
  | .return e? => .return (ExprRewriter.rewrite_expr f e?)
  | .error e => .error (ExprRewriter.rewrite_expr f e)

def BlockExit.rewriteM_expr [Monad m]
    (f : Expr → m Expr) (exit : BlockExit) : m BlockExit := do
  match exit with
  | .jump lbl => return .jump lbl
  | .cjump t hotpath tt ff => return .cjump t hotpath tt ff
  | .return e? => return .return (← ExprRewriter.rewriteM_expr f e?)
  | .error e => return .error (← ExprRewriter.rewriteM_expr f e)

instance : ExprRewriter BlockExit where
  rewrite_expr := BlockExit.rewrite_expr
  rewriteM_expr := BlockExit.rewriteM_expr

@[instance_reducible]
def Block.rewrite_expr (f : Expr → Expr) (b : Block) : Block :=
  { b with body := ExprRewriter.rewrite_expr f b.body,
           exit := ExprRewriter.rewrite_expr f b.exit }

def Block.rewriteM_expr [Monad m]
    (f : Expr → m Expr) (b : Block) : m Block := do
  return { b with
    body := ← ExprRewriter.rewriteM_expr f b.body,
    exit := ← ExprRewriter.rewriteM_expr f b.exit
  }

@[instance_reducible]
def Block.rewrite_stmt (f : Stmt → Option Stmt) (b : Block) : Block :=
  { b with body := b.body.filterMap f }

def Block.rewriteM_stmt [Monad m]
    (f : Stmt → m (Option Stmt)) (b : Block) : m Block := do
  return { b with body := ← b.body.filterMapM f }

instance : ExprRewriter Block where
  rewrite_expr := Block.rewrite_expr
  rewriteM_expr := Block.rewriteM_expr

instance : StmtRewriter Block where
  rewrite_stmt := Block.rewrite_stmt
  rewriteM_stmt := Block.rewriteM_stmt

def Func.rewrite_expr (f : Expr → Expr) (func : Func) : Func :=
  { func with blocks := func.blocks.map (fun _ => ExprRewriter.rewrite_expr f) }

def Func.rewriteM_expr [Monad m]
    (f : Expr → m Expr) (func : Func) : m Func := do
  let blocks ← func.blocks.toList.mapM (fun (l, b) => do
    return (l, ← ExprRewriter.rewriteM_expr f b)
  )
  return { func with blocks := Std.HashMap.ofList blocks }

def Func.rewrite_stmt (f : Stmt → Option Stmt) (func : Func) : Func :=
  { func with blocks := func.blocks.map (fun _ => StmtRewriter.rewrite_stmt f) }

def Func.rewriteM_stmt [Monad m]
    (f : Stmt → m (Option Stmt)) (func : Func) : m Func := do
  let blocks ← func.blocks.toList.mapM (fun (l, b) => do
    return (l, ← StmtRewriter.rewriteM_stmt f b)
  )
  return { func with blocks := Std.HashMap.ofList blocks }

instance : ExprRewriter Func where
  rewrite_expr := Func.rewrite_expr
  rewriteM_expr := Func.rewriteM_expr

instance : StmtRewriter Func where
  rewrite_stmt := Func.rewrite_stmt
  rewriteM_stmt := Func.rewriteM_stmt

def Prog.rewrite_expr (f : Expr → Expr) (p : Prog) : Prog :=
  { p with funcs := ExprRewriter.rewrite_expr f p.funcs }

def Prog.rewriteM_expr [Monad m]
    (f : Expr → m Expr) (p : Prog) : m Prog := do
  return { p with funcs := ← ExprRewriter.rewriteM_expr f p.funcs }

def Prog.rewrite_stmt (f : Stmt → Option Stmt) (p : Prog) : Prog :=
  { p with funcs := StmtRewriter.rewrite_stmt f p.funcs }

def Prog.rewriteM_stmt[Monad m]
    (f : Stmt → m (Option Stmt)) (p : Prog) : m Prog := do
  return { p with funcs := ← StmtRewriter.rewriteM_stmt f p.funcs }

instance : ExprRewriter Prog where
  rewrite_expr := Prog.rewrite_expr
  rewriteM_expr := Prog.rewriteM_expr

instance : StmtRewriter Prog where
  rewrite_stmt := Prog.rewrite_stmt
  rewriteM_stmt := Prog.rewriteM_stmt
