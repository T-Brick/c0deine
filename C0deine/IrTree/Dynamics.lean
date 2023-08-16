import C0deine.AuxDefs
import C0deine.IrTree.IrTree

namespace C0deine.Dynamics

open IrTree

inductive Exception
| memory
| arithmetic

inductive Value : Expr → Prop
| byte  : Value (.byte b)
| const : Value (.const i)

def ExprValues := { e : Expr // Value e }

inductive DynResult : Prop
| value : ExprValues → DynResult
| eval : Expr → List Stmt → DynResult
| exec : Stmt → List Stmt → DynResult
| exception : Exception → DynResult


notation:50 lhs:51 " ▷ " rhs:51 => DynResult.eval lhs rhs
notation:50 lhs:51 " ▸ " rhs:51 => DynResult.exec lhs rhs

def Environment := Temp.Map ExprValues
def Environment.empty : Environment := Temp.Map.empty

structure StackFrame where
  environment : Environment
  continuation : List Stmt

def StackFrame.empty : StackFrame :=
  { environment := Environment.empty
  , continuation := []
  }

structure Heap where
  data : Std.HashMap Nat ExprValues
  next : Nat

def Heap.empty : Heap :=
  { data := Std.HashMap.empty
  , next := 0
  }

-- inductive ExprEval (H : Heap) (S : List StackFrame) (η : Environment) : Expr → List Stmt → DynResult → Prop
-- | byte : ExprEval H S η (.byte b)
