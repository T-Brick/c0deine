
namespace C0deine

def Temp := Nat
deriving DecidableEq, Inhabited, Hashable

namespace Temp

instance : ToString Temp where
  toString | t => s!"%t{show Nat from t}"

end Temp
