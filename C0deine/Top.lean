/- C0deine - Top
   Parsing CLI args as well as weaving all the different phases/translations
   together.
   - Thea Brick
   - James Gallicchio
-/
import C0deine
import Cli

namespace C0deine.Top

def version := "v24.01.1"

open Cli Directive

def mkConfig (p : Parsed)
             (libSearchDirs : List System.FilePath)
             (input : System.FilePath)
             : Config :=
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
      output                 := output
      libSearchDirs          := libSearchDirs
      typecheckOnly          := p.hasFlag "only-typecheck"
      safe                   := ¬p.hasFlag "unsafe"
      checkAssertsWhenUnsafe := p.hasFlag "unsafe-assert-check"
      dynCheckContracts      := p.hasFlag "dyn-check"
      contractPurity         := ¬p.hasFlag "no-purity-check"
      dumpWasmHex            := p.hasFlag "dump-wasm"
  }

def mkWasmConfig (p : Parsed) : Wasm.Config :=
  let dconfig : Wasm.Config := default
  { dconfig with
      import_calloc := p.hasFlag "wasm-import-calloc"
      include_debug := p.hasFlag "wasm-debugger"
  }

def outputText (config : Config) (data : String) : IO Unit :=
  match config.output with
  | .none   => IO.println data
  | .some f => IO.FS.writeFile f data

def outputBinary (config : Config) (data : ByteArray) : IO Unit := do
  if config.dumpWasmHex then
    IO.print "!wasm-dump: "
    let out := data.data.toList.map UInt8.toHexNumString
    IO.println (" ".intercalate out)
  else
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

  let libs : List System.FilePath :=
    p.flag? "library" |>.map (·.as! (Array String) |>.toList) |>.getD []
  let libSearchDirs : List System.FilePath :=
    p.flag? "L" |>.map (·.as! (Array String) |>.toList) |>.getD []

  let curDir ← IO.currentDir
  let libSearchDirs := curDir :: libSearchDirs
  let libSearchDirs :=
    if (← (curDir / "libs").pathExists) && (← (curDir / "libs").isDir) then
      curDir / "libs" :: libSearchDirs
    else libSearchDirs

  let _ ← libs.mapM (fun lib => do
      if !(← lib.pathExists) then
        panic! s!"Library file does not exist: {lib}"
      if ← lib.isDir then
        panic! s!"Library file is a directory: {lib}"
    )

  let _ ← libSearchDirs.mapM (fun libd => do
      if !(← libd.pathExists) then
        panic! s!"Library search directory does not exist: {libd}"
      if !(← libd.isDir) then
        panic! s!"Library search directory is not a directory: {libd}"
    )

  let cl_program := p.hasFlag "cl-program"

  let inputs : List System.FilePath ← do
    if cl_program then pure [] else
    let inputs : List System.FilePath ←
      p.variableArgsAs! String |>.toList |>.mapM (Use.mkAbsolute)
    if inputs.isEmpty then panic! "Must provide a file input"
    pure inputs

  let cl_src? : Option String :=
    if cl_program then
      " ".intercalate (p.variableArgsAs! String |>.toList)
      |>.replace "\\\\n" "$newline"   -- convert `\\n` to `$newline`
      |>.replace "\\n" "\n"
      |>.replace "$newline" "\\n"     -- restore newlines
    else none

  let _ ← inputs.mapM (fun input => do
    if !(← input.pathExists) then
      panic! s!"Input file does not exist: {input}"
    if ← input.isDir then
      panic! s!"Input path is a directory: {input}"
  )

  let libSearchDirs := libSearchDirs ++ (inputs.filterMap (·.parent))
    |>.eraseDups

  let config : Config :=
    mkConfig p libSearchDirs (inputs.get? 0 |>.getD "default.c0")
  let inputsCat := inputs.map (Config.Library.src)
  let libsCat :=
    (← libs.mapM (Use.find_lib config ·.toString)).join |>.eraseDups
  let cats := (inputsCat.reverse ++ libsCat).reverse
  let files := inputs ++ libs

  let sources ←
    match cl_src? with
    | some src => Use.find_files_from_source config [] cats files src
    | none     => Use.find_files_from_file config [] cats files

  let init_parsed : Use.ParsedC0 :=
    ⟨config, [], [], .empty, .new (¬config.lang.under .c0)⟩

  let parsed ← sources.foldlM (fun acc f =>
      match f with
      | .std l h =>
        let config := { acc.config with stdLibs := l :: acc.config.stdLibs }
        Use.parseHeaderFile {acc with config} h
      | .src s   => Use.parseFile acc s
      | .head h  => Use.parseHeaderFile acc h
    ) init_parsed

  -- if program was passed on the command line load it here
  let parsed ← do
    match cl_src? with
    | .some src => Use.parseSource parsed src
    | .none     => pure parsed


  let vprintln : {α : Type} → [ToString α] → α → IO Unit :=
    fun s => do if config.verbose then IO.println s
  let vcprintln : {α : Type} → [ToString α] → Bool → α → IO Unit :=
    fun b s => do if b || config.verbose then IO.println s

  let config := parsed.config
  let wasm_config := mkWasmConfig p
  let ctx := parsed.ctx
  -- vprintln cst
  vprintln "abstracting"

  let ast ← IO.ofExcept <|
    Abstractor.abstract config.lang (parsed.header) (parsed.source)

  vprintln ast
  vprintln "typechecking"

  match Typechecker.typecheck ast with
  | .error e =>
    IO.println s!"\n{e}\n"
    return 1
  | .ok tst =>

  vprintln "typechecked!"
  vcprintln (p.hasFlag "dump-tst") tst

  if config.typecheckOnly then return 0

  vprintln "ir translation..."
  let (irtree, _ctx) := IrTree.Trans.prog config tst ctx
  vprintln "ir tree!"
  vcprintln (p.hasFlag "dump-ir") irtree

  vprintln "building cfgs..."
  let cfgs := IrTree.Prog.to_cfgs irtree
  vprintln "cfgs!"
  vcprintln (p.hasFlag "dump-cfg") cfgs

  if ¬config.emit.isWasmFormat then
    IO.println s!"Emit language {config.emit} not yet supported"
    return 1

  vprintln "relooping cfgs..."
  let relooped := cfgs.map ControlFlow.Relooper.reloop
  vprintln "relooped!"
  vcprintln (p.hasFlag "dump-cfg") relooped

  vprintln "wasm translation..."
  let wasm := Target.Wasm.Trans.prog wasm_config irtree (relooped.filterMap (·))
  let data := Target.Wasm.Trans.data irtree
  let libs := config.stdLibs.map (·.toWasmLib)
  let wasm_module_cst := Target.Wasm.mkModule wasm_config libs wasm data
  vprintln "wasm!"

  if let .wat := config.emit then
    outputText config wasm_module_cst.toString
  if let .wasm := config.emit then
    vcprintln (p.hasFlag "dump-wat") wasm_module_cst
    match (Wasm.Text.Module.trans wasm_module_cst).run ⟨{}, []⟩ with
    | (.error e, _state) =>
      IO.println "Internal WASM translation error!"
      IO.println ("\n".intercalate e.log.reverse)
      return 1
    | (.ok wasm_module_ast, _) =>
      -- vprintln (toString (wasm_module_ast : Wasm.Text.Module))
      let arr_byte := (Wasm.Binary.Module.toOpcode wasm_module_ast).toArray
      outputBinary config ⟨arr_byte⟩


  return 0

def topCmd : Cmd := `[Cli|
  c0deine VIA runTopCmd; [version]
  "a compiler for C0."

  FLAGS:
    l, library : Array String; "Specifies libraries to include (comma separated)"
    L, L : Array String;       "Add library directories to search path (comma separated)"
    v, verbose;                "Give verbose output"
    x, lang : String;          "Source language (usually derived from filename)"
    e, emit : String;          s!"Specify compilation target\n{Target.supported_str}"
    t, "only-typecheck";       "Only typecheck a file"
    o, output : String;        "Output to given file"
    -- O0, O0;                    "Compile with no optimizations"
    -- O1, O1;                    "Compile with optimizations"
    "unsafe";                  "Assume code does not make memory/division errors"
    "unsafe-assert-check";     "Requires checking asserts when unsafe"
    d, "dyn-check";            "Check contracts dynamically (not implemented)"
    "no-purity-check";         "Disables contract purity checking"
    "wasm-debugger";           "Include calls to c0deine.debug in WASM"
    "wasm-import-calloc";      "WASM outputs require importing 'c0deine.calloc' and 'c0deine.free'"
    "dump-tst";                "Dumps the TST to stdout"
    "dump-ir";                 "Dumps the IR to stdout"
    "dump-cfg";                "Dumps the CFG information to stdout"
    "dump-wat";                "Dumps the WAT to stdout"
    "dump-wasm";               "Dumps the WASM bytecode to stdout"
    "cl-program";              "Program is passed in as a string in the input instead of as a filepath"

  ARGS:
    ...inputs : String;      "The input files"
]
