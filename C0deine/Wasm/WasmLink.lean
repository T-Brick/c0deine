/- C0deine - WasmLink
   Takes the individual WASM components and links them together into a valid
   WASM module.
   - Thea Brick
 -/
import C0deine.Wasm.Wasm
import C0deine.Config.Language
import C0deine.Wasm.Library.Conio
import C0deine.Wasm.Library.Parse
import C0deine.Wasm.Library.String

namespace C0deine.Target.Wasm

open Wasm.Text

open Library in
def _root_.C0deine.Language.StdLib.toWasmLib : Language.StdLib → Library
  | .conio  => Conio
  | .file   => panic "ERR: No implementation for 'file' library!"
  | .args   => panic "ERR: No implementation for 'args' library!"
  | .parse  => Parse
  | .string => String
  | .img    => panic "ERR: No implementation for 'img' library!"
  | .rand   => panic "ERR: No implementation for 'rand' library!"
  | .util   => panic "ERR: No implementation for 'util' library!"

def mkImports (config : Wasm.Config)
              (libs : List Library)
              : List (Module.Field) :=
  [ .some memory_import
  , .some result_import
  , .some error_import
  , if config.import_abort  then .some abort_import  else .none
  , if config.import_calloc then .some calloc_import else .none
  , if config.import_calloc then .some free_import   else .none
  , if config.include_debug then .some debug_import  else .none
  , match config.main with | .import => .some main_import | _ => .none
  ].filterMap (·) ++ libs.flatMap (·.imports)

def mkModule (config : Wasm.Config)
             (libs : List Library)
             (funcs : List Module.Function)
             (data : Module.Data)
             : Module :=
  let c0_funcs := funcs.map .funcs
  ⟨ .none
  , mkImports config libs
    ++ [ if config.import_calloc then .none else .some calloc_func
       , if config.import_calloc then .none else .some free_func
       , if config.import_abort then .none else .some abort_func
       ].filterMap (·)
    ++ [.datas data]
    ++ (main config)
    ++ (libs.flatMap (·.intern))
    ++ (libs.flatMap (·.extern))
    ++ c0_funcs
  ⟩
