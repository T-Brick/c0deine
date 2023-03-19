import C0deine
import Cli

namespace C0deine.Top

def version := "0.0.1"

open Cli

def runTopCmd (p : Parsed) : IO UInt32 := do
  if !p.hasPositionalArg "input" then
    panic! "missing file argument"
  let input : System.FilePath := p.positionalArg! "input" |>.as! String
  let tcOnly : Bool := p.hasFlag "typecheck"

  if !(← input.pathExists) then
    panic! "input file does not exist"
  if ← input.isDir then
    panic! "input path is a directory"
  
  let lang : Language :=
    match input.extension with
    | none => panic! "file is missing extension"
    | some "l1" => .l1
    | some "l2" => .l2
    | some "l3" => .l3
    | some "l4" => .l4
    | some "c0" => .c0
    | some "c1" => .c1
    | some x => panic! s!"unrecognized extension {x}"

  let contents ← IO.FS.readFile input

  match (Parser.C0Parser.prog <* Parser.endOfInput).run contents.toSubstring Context.State.new with
  | (.error e, _)
  | (.ok (.error e), _) =>
    panic! s!"parser error: {e}"
  | (.ok (.ok _ cst), ctx) =>
  
  let ast ← IO.ofExcept <| Abstractor.abstract lang cst
  
  match (Typechecker.typecheck ast).run ctx with
  | (.error e, _) =>
    panic! s!"{e}"
  | (.ok x, ctx) =>

  if tcOnly then return 0

  IO.println "typechecked!"
  IO.println x

  return 0

def topCmd : Cmd := `[Cli|
  c0deine VIA runTopCmd; [version]
  "a compiler for C0."

  FLAGS:
    t, typecheck;               "Only typecheck a file"
    v, verbose;                 "Give verbose output"
    e, emit : String;           "Specify compilation target (either x86 or wasm)"
    l, library : String;        "Specify header file"
    O0;                         "Compile with no optimizations"
    O1;                         "Compile with optimizations"


  ARGS:
    input : String;      "The input file"
]