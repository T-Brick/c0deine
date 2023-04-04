
import C0deine.Utils.ValueSize

namespace C0deine

def Temp := Nat
deriving DecidableEq, Inhabited, Hashable

namespace Temp

instance : ToString Temp where
  toString | t => s!"%t{show Nat from t}"

end Temp

def SizedTemp := Sized Temp

def SizedTemp.temp (stemp : SizedTemp) : Temp := stemp.data
def SizedTemp.toString (stemp : SizedTemp) : String :=
  s!"%t{stemp.size}{show Nat from stemp.temp}"
instance : ToString SizedTemp where toString := SizedTemp.toString
