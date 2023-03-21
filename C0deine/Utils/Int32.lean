import Std

/-! Signed 32-bit integers, encoded as UInt32 -/
namespace C0deine

@[irreducible] def Int32 := UInt32
deriving Inhabited

namespace Int32

@[inline] def ofUInt32 : UInt32 → Int32 := cast (by unfold Int32; rfl) id

@[inline] def toUInt32 : Int32 → UInt32 := cast (by unfold Int32; rfl) id

def MAX : Int32 := ofUInt32 <| .ofNat (2^31 - 1)
def MIN : Int32 := ofUInt32 <| .ofNat (2^31)

def toInt (i : Int32) : Int :=
  if i.toUInt32 < MIN.toUInt32 then -- i pos
    i.toUInt32.toNat
  else
    -(0 - i.toUInt32).toNat

def ofInt? (i : Int) : Option Int32 :=
  let offset := i + (2^31 : Nat)
  if h:0 ≤ offset && offset < UInt32.size then
    let offset : UInt32 := ⟨offset.natAbs, by
      simp at *
      have := Int.natAbs_lt_natAbs_of_nonneg_of_lt h.1 h.2
      exact this⟩
    ofUInt32 (offset + .ofNat (2^31))
  else
    none

def ofNat? (n : Nat) : Option Int32 := ofInt? n

instance : OfNat Int32 n := ⟨.ofUInt32 <| .ofNat n⟩

instance : Coe Int32 Int := ⟨toInt⟩
instance : ToString Int32 := ⟨toString ∘ toInt⟩
instance : Repr Int32 := ⟨reprPrec ∘ toInt⟩

def decEq : (a b : Int32) → Decidable (a = b) := cast (by unfold Int32; rfl) UInt32.decEq
instance : DecidableEq Int32 := decEq

def add : Int32 → Int32 → Int32 := cast (by unfold Int32; rfl) UInt32.add
instance : Add Int32 := ⟨add⟩

def sub : Int32 → Int32 → Int32 := cast (by unfold Int32; rfl) UInt32.sub
instance : Sub Int32 := ⟨sub⟩

def neg : Int32 → Int32 := fun i => ofUInt32 0 - i
instance : Neg Int32 := ⟨neg⟩

def mul : Int32 → Int32 → Int32 := cast (by unfold Int32; rfl) UInt32.mul
instance : Mul Int32 := ⟨mul⟩

nonrec def compare (i j : Int32) : Ordering :=
  let i := i.toUInt32
  let j := j.toUInt32
  if i < MIN.toUInt32 then -- i pos
    if j < MIN.toUInt32 then -- j pos
      compare i j
    else -- j neg
      .gt
  else -- i neg
    if j < MIN.toUInt32 then -- j pos
      .lt
    else -- j neg
      compare i j
instance : Ord Int32 := ⟨compare⟩

def divExn (i j : Int32) : Except Unit Int32 :=
  match compare (ofUInt32 0) j with
  | .eq => throw ()
  | .lt => .ok <| ofUInt32 (i.toUInt32 / j.toUInt32)
  | .gt => .ok <| (-ofUInt32 (i.toUInt32 / (-j).toUInt32))

instance : HDiv Int32 Int32 (Except Unit Int32) := ⟨divExn⟩
