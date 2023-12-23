/- C0deine - Conio
   WASM for C0's "conio" standard library. Currently, `printf` is not
   implemented since that requires variadic functions.
   - Thea Brick
 -/
import C0deine.Wasm.Library.Util

namespace C0deine.Target.Wasm.Library.Conio

open Numbers C0deine.Target.Wasm Wasm.Text Wasm.Text.Instr
  Wasm.Syntax.Instr.Numeric Wasm.Syntax.Instr.Memory

def print_id     : Ident := ⟨"_c0_print"    , sorry, sorry⟩
def println_id   : Ident := ⟨"_c0_println"  , sorry, sorry⟩
def printint_id  : Ident := ⟨"_c0_printint" , sorry, sorry⟩
def printbool_id : Ident := ⟨"_c0_printbool", sorry, sorry⟩
def printchar_id : Ident := ⟨"_c0_printchar", sorry, sorry⟩
def flush_id     : Ident := ⟨"_c0_flush"    , sorry, sorry⟩
def eof_id       : Ident := ⟨"_c0_eof"      , sorry, sorry⟩
def readline_id  : Ident := ⟨"_c0_readline" , sorry, sorry⟩
def printf_id    : Ident := ⟨"_c0_printf"   , sorry, sorry⟩

def conio : Name :=
  ⟨"conio", by simp [String.length, Wasm.Vec.max_length]; linarith⟩

/- print : string → unit -/
def print : Module.Field := .imports
  ⟨ conio
  , ⟨ print_id.name, by
      simp [print_id, Ident.name, String.length, Wasm.Vec.max_length]
      linarith
    ⟩
  , .func (.some print_id) (.elab_param_res [(.none, .num .i32)] [])
  ⟩

/- println : string → unit -/
def println : Module.Field := .imports
  ⟨ conio
  , ⟨ println_id.name, by
      simp [println_id, Ident.name, String.length, Wasm.Vec.max_length]
      linarith
    ⟩
  , .func (.some println_id) (.elab_param_res [(.none, .num .i32)] [])
  ⟩

/- printint : int → unit -/
def printint : Module.Field := .funcs
  { lbl     := .some printint_id
  , typeuse := .elab_param_res [(.none, .num .i32)] []
  , locals  := []
  , body    := Util.string_fromint ++
    [ locl (.get 0)
    , Plain.call print_id
    , Plain.wasm_return
    ]
  }

/- printbool : bool → unit -/
def printbool : Module.Field := .funcs
  { lbl     := .some printbool_id
  , typeuse := .elab_param_res [(.none, .num .i32)] []
  , locals  := []
  , body    := Util.string_frombool ++
    [ locl (.get 0)
    , Plain.call print_id
    , Plain.wasm_return
    ]
  }

/- printchar : char → unit -/
def printchar : Module.Field := .funcs
  { lbl     := .some printchar_id
  , typeuse := .elab_param_res [(.none, .num .i32)] []
  , locals  := [⟨.none, .num .i32⟩]
  , body    := Util.string_fromchar ++
    [ locl (.get 1)
    , Plain.call print_id
    ]
  }

/- flush : unit → unit -/
def flush : Module.Field := .imports
  ⟨ conio
  , ⟨ flush_id.name, by
      simp [flush_id, Ident.name, String.length, Wasm.Vec.max_length]
      linarith
    ⟩
  , .func (.some flush_id) (.elab_param_res [] [])
  ⟩

/- eof : unit → bool -/
def eof : Module.Field := .imports
  ⟨ conio
  , ⟨ eof_id.name, by
      simp [eof_id, Ident.name, String.length, Wasm.Vec.max_length]
      linarith
    ⟩
  , .func (.some eof_id) (.elab_param_res [] [.num .i32])
  ⟩

/- readline : unit → string -/
def readline : Module.Field := .imports
  ⟨ conio
  , ⟨ readline_id.name, by
      simp [readline_id, Ident.name, String.length, Wasm.Vec.max_length]
      linarith
    ⟩
  , .func (.some readline_id) (.elab_param_res [] [.num .i32])
  ⟩

/- printf : string × ...args → unit
   Not currently implemented.
 -/
def printf : Module.Field := .imports
  ⟨ conio
  , ⟨ printf_id.name, by
      simp [printf_id, Ident.name, String.length, Wasm.Vec.max_length]
      linarith
    ⟩
  , .func (.some printf_id) (.elab_param_res [] [.num .i32])
  ⟩

def imports : List Module.Field :=
  [ print
  , println
  , flush
  , eof
  , readline
  -- , printf
  ]
def extern : List Module.Field :=
  [ printint
  , printbool
  , printchar
  ]
def intern : List Module.Field := []
def lib    : List Module.Field := imports ++ intern ++ extern

end Conio

def Conio : Library :=
  { imports := Conio.imports
  , extern  := Conio.extern
  , intern  := Conio.intern
  , lib     := Conio.lib
  }
