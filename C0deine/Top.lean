/- C0deine - Top
   Parsing CLI args as well as weaving all the different phases/translations
   together.
   - Thea Brick
   - James Gallicchio
-/
import C0deine
import Cli

namespace C0deine.Top

def version := "0.0.1"

open Cli

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

def outputText (config : Config) (data : String) : IO Unit :=
  match config.output with
  | .none   => IO.println data
  | .some f => IO.FS.writeFile f data

def outputBinary (config : Config) (data : ByteArray) : IO Unit := do
  if config.dumpWasmHex then
    IO.print "!wasm-dump: "
    let out := data.data.toList.map UInt8.toHexNumString
    IO.println (" ".intercalate out)
  match config.output with
  | .none   => panic! "Cannot write binary to stdout"
  | .some f => IO.FS.writeBinFile f data

def searchDirs (dirs : List System.FilePath)
               (file : String) : IO (Option System.FilePath) :=
  match dirs with
  | [] => return .none
  | d :: rest => do
    if (← (d / file).pathExists)
    then return .some (d / file)
    else searchDirs rest file

def find_lib (config : Config) (s : String) : IO (List Config.Library) := do
  match Language.StdLib.ofString s with
  | .some l =>
    let path? ← searchDirs config.libSearchDirs (l.toHeaderString)
    match path? with
    | .some path => return [.std l path]
    | .none      => panic s!"Could not find Standard Library header: {l}"
  | .none   =>
    let srcName  :=
      System.FilePath.withExtension s (config.lang.toString) |>.toString
    let headName :=
      System.FilePath.withExtension s (config.lang.toHeaderString) |>.toString

    let src_path? ← searchDirs config.libSearchDirs srcName
    let head_path? ← searchDirs config.libSearchDirs headName

    match src_path?, head_path? with
    | .some src_path, .some head_path =>
      return [.head head_path, .src src_path]
    | .some src_path, .none  => return [.src src_path]
    | .none, .some head_path => return [.head head_path]
    | .none, .none           => panic s!"Could not find library: {s}"


def find_use_file (config : Config) : Cst.Directive → IO (List Config.Library)
  | .use_lib s => find_lib config s
  | .use_str s => do
    let path? ← searchDirs config.libSearchDirs s
    match path?.bind (Config.Library.ofPath ·) with
    | .some res => return [res]
    | .none      => panic s!"Could not find library: {s}"

  | .unknown => return []

partial def find_files
    (config : Config)
    (imported : List System.FilePath)
    (acc : List Config.Library)
    (files : List System.FilePath)
    : IO (List Config.Library) := do
  match files with
  | [] => return acc
  | l :: rest =>
    if l ∈ imported then find_files config imported acc rest else

    if !(← l.pathExists) then
      panic! s!"File does not exist: {l}"
    if ← l.isDir then
      panic! s!"File is a directory: {l}"

    let contents ← IO.FS.readFile l
    match Parser.C0Parser.directives.run contents.toUTF8 (.new false) with
    | ((.error e, state), _) =>
      IO.println s!"{e () |>.formatPretty state}"
      panic s!"Could not parse directives!"
    | ((.ok refs, _), _) =>
      let refs := (← refs.mapM (find_use_file config)).join
        |>.filter (· ∉ acc)
        |>.eraseDups
      let remaining := rest ++ refs.map (·.toPath)
      find_files config (l :: imported) (refs.reverse ++ acc) remaining

-- todo monadify this
structure ParsedC0 where
  config : Config
  header : Cst.Prog
  source : Cst.Prog
  tydefs : Std.RBSet Symbol compare
  ctx : Context.State

def parseHeaderFile
    (acc : ParsedC0)
    (header : System.FilePath)
    : IO ParsedC0 := do
  if acc.config.verbose then IO.println s!"Parsing header {header}"
  let h ← IO.FS.readFile header
  match (Parser.C0Parser.prog acc.tydefs).run h.toUTF8 acc.ctx with
  | ((.error e, state), _) =>
    IO.println s!"{e () |>.formatPretty state}"
    panic s!"Header parse error"
  | ((.ok (cst, tydefs), _), ctx) =>
    let (_directives, cst) := Cst.splitDirectives cst
    pure ⟨acc.config, acc.header ++ cst, acc.source, tydefs, ctx⟩

def parseSource
    (acc : ParsedC0)
    (c : String)
    : IO ParsedC0 := do
  match (Parser.C0Parser.prog acc.tydefs).run c.toUTF8 acc.ctx with
  | ((.error e, state), _) =>
    IO.println s!"{e () |>.formatPretty state}"
    panic s!"Source parse error"
  | ((.ok (cst, tydefs), _), ctx) =>
    let (_directives, cst) := Cst.splitDirectives cst
    pure ⟨acc.config, acc.header, acc.source ++ cst, tydefs, ctx⟩

def parseFile
    (acc : ParsedC0)
    (source : System.FilePath)
    : IO ParsedC0 := do
  if acc.config.verbose then IO.println s!"Parsing source {source}"
  let c ← IO.FS.readFile source
  parseSource acc c

def runTopCmd (p : Parsed) : IO UInt32 := do
  if p.hasFlag "help" then
    p.printHelp
    return 0
  if p.hasFlag "version" then
    p.printVersion!
    return 0

  let inputs : List System.FilePath :=
    p.variableArgsAs! String |>.toList
  if inputs.isEmpty then panic! "Must provide a file input"

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

  let _ ← inputs.mapM (fun input => do
    if !(← input.pathExists) then
      panic! s!"Input file does not exist: {input}"
    if ← input.isDir then
      panic! s!"Input path is a directory: {input}"
  )

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

  let config : Config := mkConfig p libSearchDirs (inputs.get! 0)
  let inputsCat := inputs.map (Config.Library.src)
  let libsCat := (← libs.mapM (find_lib config ·.toString)).join |>.eraseDups

  let sources ←
    find_files config [] (inputsCat.reverse ++ libsCat).reverse
      (inputs ++ libs)

  let vprintln : {α : Type} → [ToString α] → α → IO Unit :=
    fun s => do if config.verbose then IO.println s

  let init_parsed : ParsedC0 :=
    ⟨config, [], [], .empty, .new (¬config.lang.under .c0)⟩
  let parsed ← sources.foldlM (fun acc f =>
      match f with
      | .std l h =>
        let config := { acc.config with stdLibs := l :: acc.config.stdLibs }
        parseHeaderFile {acc with config} h
      | .src s   => parseFile acc s
      | .head h  => parseHeaderFile acc h
    ) init_parsed
  let config := parsed.config
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
  let libs := config.stdLibs.map (·.toWasmLib)
  let wasm_module_cst := Target.Wasm.mkModule default libs wasm data
  vprintln "wasm!"

  if let .wat := config.emit then
    outputText config wasm_module_cst.toString
  if let .wasm := config.emit then
    vprintln wasm_module_cst
    match (Wasm.Text.Module.trans wasm_module_cst).run ⟨{}, []⟩ with
    | (.error e, _state) =>
      IO.println "Internal WASM translation error!"
      IO.println ("\n".intercalate e.log.reverse)
      return 1
    | (.ok wasm_module_ast, _) =>
      vprintln (toString (wasm_module_ast : Wasm.Text.Module))
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
    d, "dyn-check";            "Check contracts dynamically"
    "no-purity-check";         "Disables contract purity checking"
    "wasm-import-calloc";      "WASM outputs require importing 'c0deine.calloc' and 'c0deine.free'"
    "dump-wasm";               "Dumps the WASM bytecode to stdout"

  ARGS:
    ...inputs : String;      "The input files"
]
