
namespace C0deine

def Label := Nat
deriving DecidableEq, Inhabited

namespace Label

instance : ToString Label where
  toString | l => s!"L{show Nat from l}"

end Label
