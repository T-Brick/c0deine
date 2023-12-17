import C0deine
import Cli

namespace C0deine.Top

def version := "0.0.1"

open Cli

def mkConfig (p : Parsed) (input : System.FilePath) : Config :=
  let dconfig : Config := default

  let lang :=
    match p.flag? "lang" |>.map (·.as! String) with
    | .some str =>
      match Language.ofString str with
      | .some l => l
      | .none   => panic! s!"Unknowning language target: {str}"
    | .none   =>
      match input.extension with
      | .none   => panic! "File is missing extension"
      | .some l =>
        match Language.ofString l with
        | .some l => l
        | .none   => panic! s!"Unrecognized extension/language {l}"

  let emit :=
    match p.flag? "emit" |>.map (·.as! String) with
    | .some str =>
      match Target.ofString str with
      | .some e => e
      | .none   => panic! s!"Unknowning emit target: {str}"
    | .none   => dconfig.emit

  let output :=
    match p.flag? "output" |>.map (·.as! String) with
    | .some o => some o
    | .none   =>
      if emit.isBinaryFormat
      then some (input.withExtension emit.toString)
      else dconfig.output

  { dconfig with
      verbose                := p.hasFlag "verbose"
      lang                   := lang
      emit                   := emit
      typecheckOnly          := p.hasFlag "only-typecheck"
      output                 := output
      safe                   := ¬p.hasFlag "unsafe"
      checkAssertsWhenUnsafe := p.hasFlag "unsafe-assert-check"
      dynCheckContracts      := p.hasFlag "dyn-check"
      contractPurity         := ¬p.hasFlag "no-purity-check"
  }

def outputText (config : Config) (data : String) : IO Unit :=
  match config.output with
  | .none   => IO.println data
  | .some f => IO.FS.writeFile f data

def outputBinary (config : Config) (data : ByteArray) : IO Unit :=
  match config.output with
  | .none   => panic! "Cannot write binary to stdout"
  | .some f => IO.FS.writeBinFile f data

def runTopCmd (p : Parsed) : IO UInt32 := do
  if p.hasFlag "help" then
    p.printHelp
    return 0
  if p.hasFlag "version" then
    p.printVersion!
    return 0

  if !p.hasPositionalArg "input" then
    panic! "Missing file argument"
  let input : System.FilePath :=
    p.positionalArg! "input" |>.as! String
  let libInput : Option System.FilePath :=
    p.flag? "library" |>.map (·.as! String)

  if !(← input.pathExists) then
    panic! s!"Input file does not exist: {input}"
  if ← input.isDir then
    panic! s!"Input path is a directory: {input}"

  if libInput.isSome then
    if !(← libInput.get!.pathExists) then
      panic! s!"Header file does not exist: {libInput}"
    if ← libInput.get!.isDir then
      panic! s!"Header path is a directory: {libInput}"

  let config : Config := mkConfig p input

  let vprintln : {α : Type} → [ToString α] → α → IO Unit :=
    fun s => do if config.verbose then IO.println s


  let contents ← IO.FS.readFile input
  let header ← libInput.mapM (IO.FS.readFile)

  vprintln "parsing header"

  let (header, headerTydefs, ctx) ← do
    match header with
    | none =>
      pure (none, .empty, .new)
    | some h =>
      match Parser.C0Parser.prog.run h.toUTF8 .new with
      | ((.error e, state), _) =>
        IO.println s!"{e () |>.formatPretty state}"
        return 1
      | ((.ok (cst, tydefs), _), ctx) =>
        pure (some cst, tydefs, ctx)


  vprintln "parsing input"

  match (Parser.C0Parser.prog headerTydefs).run contents.toUTF8 ctx with
  | ((.error e, state), _) =>
    IO.println s!"{e () |>.formatPretty state}"
    return 1
  | ((.ok (cst,_), _), ctx) =>

  let (directives, cst) := Cst.splitDirectives cst


  -- vprintln cst
  vprintln "abstracting"

  let ast ← IO.ofExcept <| Abstractor.abstract config.lang header cst

  vprintln ast
  vprintln "typechecking"

  match Typechecker.typecheck ast with
  | .error e =>
    IO.println s!"\n{e}\n"
    return 1
  | .ok tst =>

  vprintln "typechecked!"
  vprintln tst

  if config.typecheckOnly then return 0

  vprintln "ir translation..."
  let (irtree, ctx) := IrTree.Trans.prog config tst ctx
  vprintln "ir tree!"
  vprintln irtree

  vprintln "building cfgs..."
  let cfgs := IrTree.Prog.to_cfgs irtree
  vprintln "cfgs!"
  vprintln cfgs

  if ¬config.emit.isWasmFormat then
    IO.println s!"Emit language {config.emit} not yet supported"
    return 1

  vprintln "relooping cfgs..."
  let relooped := cfgs.map ControlFlow.Relooper.reloop
  vprintln "relooped!"
  vprintln relooped

  vprintln "wasm translation..."
  let wasm := Target.Wasm.Trans.prog irtree (relooped.filterMap (·))
  let data := Target.Wasm.Trans.data irtree
  let wasm_module_cst := Target.Wasm.mkModule default wasm data
  vprintln "wasm!"
  vprintln wasm_module_cst

  if let .wat := config.emit then
    outputText config wasm_module_cst.toString
  if let .wasm := config.emit then
    match (Wasm.Text.Module.trans wasm_module_cst).run ⟨{}, []⟩ with
    | (.error e, _state) =>
      IO.println "Internal WASM translation error!"
      IO.println ("\n".intercalate e.log.reverse)
      return 1
    | (.ok wasm_module_ast, _) =>
      IO.println (toString (wasm_module_ast : Wasm.Text.Module))
      let arr_byte := (Wasm.Binary.Module.toOpcode wasm_module_ast).toArray
      outputBinary config ⟨arr_byte⟩


  return 0

def topCmd : Cmd := `[Cli|
  c0deine VIA runTopCmd; [version]
  "a compiler for C0."

  FLAGS:
    l, library : String;      "Specify header file"
    v, verbose;               "Give verbose output"
    x, lang : String;         "Source language (usually derived from filename)"
    e, emit : String;         s!"Specify compilation target\n{Target.supported_str}"
    t, "only-typecheck";      "Only typecheck a file"
    o, output : String;       "Output to given file"
    -- O0, O0;                   "Compile with no optimizations"
    -- O1, O1;                   "Compile with optimizations"
    "unsafe";                 "Assume code does not make memory/division errors"
    "unsafe-assert-check";    "Requires checking asserts when unsafe"
    d, "dyn-check";           "Check contracts dynamically"
    "no-purity-check";        "Disables contract purity checking"
    "wasm-import-calloc";     "WASM outputs require importing 'c0deine.calloc' and 'c0deine.free'"

  ARGS:
    input : String;      "The input file"
]
