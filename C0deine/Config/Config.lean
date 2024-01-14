/- C0deine - Config
   Settings for how the compiler should run that apply to all targets.
   - Thea Brick
 -/
import C0deine.Config.Language
import C0deine.Config.Targets

namespace C0deine

inductive Config.Setting
| ignore
| warning
| error

inductive Config.Library
| std  : Language.StdLib → (h : System.FilePath) → Library
| src  : System.FilePath → Library
| head : System.FilePath → Library
deriving Repr, Inhabited, DecidableEq

def Config.Library.toPath : Config.Library → System.FilePath
  | .std _ h => h
  | .src f   => f
  | .head h  => h

def Config.Library.ofPath (p : System.FilePath) : Option Config.Library :=
  p.extension.map (fun ext =>
    if ext.startsWith "h" then .head p else .src p
  )

instance : ToString Config.Library where
  toString
    | .std std h => s!"std:  {std} {h}"
    | .src f     => s!"src:  {f}"
    | .head h    => s!"head: {h}"

structure Config where
  verbose       : Bool
  lang          : Language
  emit          : Target
  output        : Option System.FilePath
  libSearchDirs : List System.FilePath
  stdLibs       : List Language.StdLib
  typecheckOnly : Bool
  optimisation  : Nat
  safe : Bool
  checkAssertsWhenUnsafe : Bool
  -- WIP: dynamically check contracts during runtime
  dynCheckContracts : Bool
  -- WIP: purity check contracts
  contractPurity : Bool
  dumpWasmHex : Bool
  /- WIP: In C0, `int x = x + 1` is not allowed because `x` is not declared on
     the RHS. In C, `x` is in scope. This change makes C0 follow the C standard.

     C0 would still reject `int x = x + 1` because `x` is uninitialised,
     but this change has important implications for shadowing functions:
     ```c
      int f() {
         int f = f();
         return f;
      }
     ```
     Currently, C0 accepts this program but with this change it would get
     rejected because the `f` on the RHS of the declare is not a function type.
     This makes elaboration of declares much simpler and match lecture content.
   -/
  cDeclScope : Bool
  /- WIP: Currently, statements of the form `return e; s` are allowed. Which
     creates some oddities in the semantics, and some very weird behaviour with
     variable initialisations. Specifically in the following code is accepted:
     ```c
      int y;
      return 5;
      return y;
     ```
     But this code is rejected (`y` is not initialised):
     ```c
      return 5;
      int y;
      return y;
     ```
   -/
  obviousDeadCode : Config.Setting
  /- WIP: Many students write code of the following form:
     ```c
      void foo(int *p) {
        int *m = alloc(int);
        m = p;
      }
     ```
     This is fine in C0, but with manual memory management in C this is
     an issue.
   -/
  uselessAllocs : Config.Setting

instance : Inhabited Config where default :=
  { verbose                := false
  , lang                   := default
  , emit                   := default
  , output                 := none
  , libSearchDirs          := []
  , stdLibs                := []
  , typecheckOnly          := false
  , optimisation           := 0
  , safe                   := true
  , checkAssertsWhenUnsafe := false
  , dynCheckContracts      := false
  , contractPurity         := false -- todo change when implemented
  , dumpWasmHex            := false
  , cDeclScope             := false
  , obviousDeadCode        := .ignore
  , uselessAllocs          := .ignore
  }
