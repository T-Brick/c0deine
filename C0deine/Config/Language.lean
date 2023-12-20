/- C0deine - Language
   Source languages that c0deine can use
   - Thea Brick
 -/
namespace C0deine

inductive Language
| l1    -- straight-line code
| l2    -- control-flow
| l3    -- functions, typedefs, function decs
| l4    -- memory
| c0    -- strings, chars, contracts
| c1    -- casts, function pointers, generic pointers
deriving Repr
instance : Inhabited Language where default := .c0

namespace Language

def toString : Language → String
  | l1 => "l1"
  | l2 => "l2"
  | l3 => "l3"
  | l4 => "l4"
  | c0 => "c0"
  | c1 => "c1"
instance : ToString Language where toString := Language.toString

def ofString (l : String) : Option Language :=
  match l.toLower with
  | "l1" => some l1
  | "l2" => some l2
  | "l3" => some l3
  | "l4" => some l4
  | "c0" => some c0
  | "c1" => some c1
  | _    => none

-- s2 is under s1 if s2 is a strict subset of s1
def under (s2 s1 : Language) : Bool :=
  match s1 with
  | .l1 => false
  | .l2 =>
    match s2 with
    | .l1 => true
    | _ => false
  | .l3 =>
    match s2 with
    | .l1 | .l2 => true
    | _ => false
  | .l4 =>
    match s2 with
    | .l1 | .l2 | .l3 => true
    | _ => false
  | .c0 =>
    match s2 with
    | .l1 | .l2 | .l3 | .l4 => true
    | _ => false
  | .c1 => false
