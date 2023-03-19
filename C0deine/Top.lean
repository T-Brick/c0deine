import C0deine
import Cli

namespace C0deine.Top

def version := "0.0.1"

open Cli

def runTopCmd (p : Parsed) : IO UInt32 := do
  if !p.hasPositionalArg "input" then
    panic! "missing file argument"
  let input : System.FilePath := p.positionalArg! "input" |>.as! String

  if !(← input.pathExists) then
    panic! "input file does not exist"
  if ← input.isDir then
    panic! "input path is a directory"

  let contents ← IO.FS.readFile input

  match (Parser.C0Parser.prog <* Parser.endOfInput).run contents.toSubstring Context.State.new with
  | (.error e, _) => IO.ofExcept <| .error ("parser error: " ++ toString e)
  | (.ok stx, ctx) =>
    IO.println "parsed!"
    
    return 0

def topCmd : Cmd := `[Cli|
  topCmd VIA runTopCmd; [version]
  "c0deine, a compiler for C0."

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