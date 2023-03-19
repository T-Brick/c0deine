/-
  Basic comparisons that are used throughout the compiler.
 -/
namespace C0deine

inductive Comparator
| less
| greater
| equal
| not_equal
| less_equal
| greater_equal

def Comparator.toString : Comparator → String
  | less => "l"
  | greater => "g"
  | equal => "e"
  | not_equal => "ne"
  | less_equal => "le"
  | greater_equal => "ge"
instance : ToString Comparator where toString := Comparator.toString
