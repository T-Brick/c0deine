import C0deine
import Cli

namespace C0deine.Top

def version := "0.0.1"

open Cli

def runTopCmd (p : Parsed) : IO UInt32 := do
  if !p.hasPositionalArg "input" then
    panic! "Missing file argument"
  let input : System.FilePath := p.positionalArg! "input" |>.as! String
  let tcOnly : Bool := p.hasFlag "typecheck"
  let verbose : Bool := p.hasFlag "verbose"

  if !(← input.pathExists) then
    panic! "Input file does not exist"
  if ← input.isDir then
    panic! "Input path is a directory"

  let lang : Language :=
    match input.extension with
    | none => panic! "File is missing extension"
    | some l =>
      match Language.fromString l with
      | .some lang => lang
      | .none => panic! s!"Unrecognized extension/language {l}"

  let contents ← IO.FS.readFile input

  if verbose then IO.println "parsing"

  match (Parser.C0Parser.prog <* Parser.endOfInput).run contents.toSubstring Context.State.new with
  | (.error e, _)
  | (.ok (.error e), _) =>
    panic! s!"parser error: {e}"
  | (.ok (.ok _ cst), ctx) =>

  if verbose then IO.println "abstracting"

  let ast ← IO.ofExcept <| Abstractor.abstract lang cst

  if verbose then IO.println "typechecking"

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
