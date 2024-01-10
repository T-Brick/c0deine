import C0deine.Config.Config
import C0deine.Config.Language
import C0deine.Parser.Basic

namespace C0deine.Directive.Use

def mkAbsolute (file : System.FilePath) : IO System.FilePath := do
  if file.isRelative then return (←IO.currentDir).join file else return file

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
      return [.head (← mkAbsolute head_path), .src (← mkAbsolute src_path)]
    | .some src_path, .none  => return [.src (← mkAbsolute src_path)]
    | .none, .some head_path => return [.head (← mkAbsolute head_path)]
    | .none, .none           => panic s!"Could not find library: {s}"


def find_use_file (config : Config) : Cst.Directive → IO (List Config.Library)
  | .use_lib s => find_lib config s
  | .use_str s => do
    let path? ← searchDirs config.libSearchDirs s
    match path?.bind (Config.Library.ofPath ·) with
    | .some res => return [res]
    | .none      => panic s!"Could not find library: {s}"

  | .unknown => return []


mutual
partial def find_files_from_source
    (config : Config)
    (imported : List System.FilePath)
    (acc : List Config.Library)
    (rest : List System.FilePath)
    (contents : String)
    : IO (List Config.Library) := do
  match Parser.C0Parser.directives.run contents.toUTF8 (.new false) with
  | ((.error e, state), _) =>
    IO.println s!"{e () |>.formatPretty state}"
    panic s!"Could not parse directives!"
  | ((.ok refs, _), _) =>
    let refs := (← refs.mapM (find_use_file config)).join
      |>.filter (· ∉ acc)
      |>.eraseDups
      |>.reverse
    let remaining := rest ++ refs.map (·.toPath)
    find_files_from_file config imported (refs ++ acc) remaining

partial def find_files_from_file
    (config : Config)
    (imported : List System.FilePath)
    (acc : List Config.Library)
    (files : List System.FilePath)
    : IO (List Config.Library) := do
  match files with
  | [] => return acc.eraseDups
  | l :: rest =>
    let l ← mkAbsolute l
    if l ∈ imported then find_files_from_file config imported acc rest else

    if !(← l.pathExists) then
      panic! s!"File does not exist: {l}"
    if ← l.isDir then
      panic! s!"File is a directory: {l}"

    let contents ← IO.FS.readFile l
    find_files_from_source config (l::imported) acc files contents
end

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
