/- C0deine - Comparision
   Basic comparison operators that are used in numerous IRs.
   - Thea Brick
 -/
namespace C0deine

inductive Comparator
| less
| greater
| equal
| not_equal
| less_equal
| greater_equal
deriving Repr, DecidableEq

namespace Comparator
def isEquality : Comparator → Bool
  | .equal => true
  | .not_equal => true
  | _ => false

def toString : Comparator → String
  | less => "<"
  | greater => ">"
  | equal => "=="
  | not_equal => "!="
  | less_equal => "<="
  | greater_equal => ">="
instance : ToString Comparator where toString := Comparator.toString
