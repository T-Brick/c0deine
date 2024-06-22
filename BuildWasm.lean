/-
  Copied from https://github.com/T-Brick/lean2wasm until more complete version
  is made : )
-/
import ImportGraph.Imports
import Batteries.Lean.Util.Path
import Lake

open Lean System

-- This is what we want to compile and should contain `main`
def root : Name := `Main

unsafe def main (args : List String) : IO UInt32 := do

  let is_web ←
    match args with
    | "web"::_ =>
      IO.println "Building for the web"
      pure true
    | _ =>
      IO.println "Building for local"
      pure false

  let outdir : FilePath := ".lake" / "build" / "wasm"
  if ¬ (←FilePath.pathExists outdir) then
    IO.FS.createDirAll outdir

  let wasm_tc := s!"lean-{Lean.versionString}-linux_wasm32"
  let toolchain : FilePath := "toolchains" / wasm_tc
  if ¬ (←FilePath.pathExists toolchain) then
    IO.println "Couldn't find toolchain (should be in './toolchains') will try downloading."

    let lean4_link := "https://github.com/leanprover/lean4/releases/download"
    let link := s!"{lean4_link}/v{Lean.versionString}/{wasm_tc}.tar.zst"
    let local_tar : FilePath := s!"{toolchain}.tar.zst"

    let _ ← Lake.download link local_tar |>.run
    let _ ← Lake.untar local_tar "toolchains" |>.run

  IO.println "Finding relevant dependencies..."
  /- Find relevant C-files to compile, we don't want to compile everything
      if possible because there could be unexpected name collisions and having
      less files to process significantly speeds up compilation.
  -/
  -- based on mathlib's import graph
  searchPathRef.set compile_time_search_path%
  let c_array ←
    withImportModules #[{module := root}] {} (trustLevel := 1024)
      fun env => do
        let graph := env.importGraph.filter (fun n _ =>
            -- already included in the toolchain
            ¬Name.isPrefixOf `Lean n ∧ ¬Name.isPrefixOf `Init n
          )
        let sp ← searchPathRef.get
        let sp : Lean.SearchPath := sp.map (fun p => (p / ".." / "ir"))

        let cfiles ← graph.toList.mapM (fun (mod, _) => do
            -- copied/modified hacked from Lean.findOLean
            if let some fname ← sp.findWithExt "c" mod then
              return fname
            else
              -- todo: make error msg better : )
              throw <| IO.userError s!"Could not find C for {mod}"
          )
        return cfiles.map toString |>.toArray

  IO.println s!"Found {c_array.size} files."
  IO.println "Compiling (this can take a while)..."

  -- should this just be moved into a bash script that takes the files?
  let out ← IO.Process.output {
      stdin  := .piped
      stdout := .piped
      stderr := .piped
      cmd    := "emcc"
      args   :=
       #[ "-o"
        , outdir / "c0deine.js" |>.toString
        , "-I"
        , toolchain / "include" |>.toString
        , "-L"
        , toolchain / "lib" / "lean" |>.toString
        ] ++ c_array ++
       #[ "-lInit"
        , "-lLean"
        , "-lleancpp"
        , "-lleanrt"
        , "-sFORCE_FILESYSTEM"
        ] ++ (if is_web
              then #[ "-sMODULARIZE"
                    , "-sEXPORT_NAME=c0deine"
                    , "--embed-file"
                    , "libs"
                    ]
              else #["-sNODERAWFS"]
             ) ++
       #[ "-lnodefs.js"
        , "-sEXIT_RUNTIME=1"
        , "-sMAIN_MODULE=2" -- use 2 to reduce exports to a usable amount
        , "-sLINKABLE=0"
        , "-sEXPORT_ALL=0"
        , "-sALLOW_MEMORY_GROWTH=1"
        , "-fwasm-exceptions"
        , "-pthread"
        , "-flto"
        , "-Oz"    -- takes much much longer to compile but optimises for size
        ]
    }

  IO.println out.stdout
  IO.println out.stderr

  return out.exitCode
