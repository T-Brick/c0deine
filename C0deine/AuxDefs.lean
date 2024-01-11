import Std
import Numbers
import Mathlib.Tactic

def Nat.digitCharInv! : Char → Nat
| '0' => 0
| '1' => 1
| '2' => 2
| '3' => 3
| '4' => 4
| '5' => 5
| '6' => 6
| '7' => 7
| '8' => 8
| '9' => 9
| 'a' | 'A' => 0xa
| 'b' | 'B' => 0xb
| 'c' | 'C' => 0xc
| 'd' | 'D' => 0xd
| 'e' | 'E' => 0xe
| 'f' | 'F' => 0xf
| _   => panic! "nan"

def Char.isHexDigit : Char → Bool
| '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
| 'a' | 'b' | 'c' | 'd' | 'e' | 'f'
| 'A' | 'B' | 'C' | 'D' | 'E' | 'F' => true
| _ => false

def Nat.ofDigits? (base : Nat) (s : Substring) : Option Nat :=
  s.foldl (fun acc c =>
    acc.bind fun acc =>
      if c.isHexDigit then
        let d := Nat.digitCharInv! c
        if d < base then
          some <| acc * base + d
        else
          none
      else
        none)
    (some 0)

def UInt8.toHexNumString (n : UInt8) : String :=
  let str := Nat.toHexNumString n.toNat
  if str.length == 1 then "0" ++ str else str

def Substring.toNat?' (s : Substring) : Option Nat :=
  if s.get 0 = '0' && ((s.drop 1 |>.get 0) = 'x' || (s.drop 1 |>.get 0) = 'X')
  then Nat.ofDigits? 16 (s.drop 2)
  else Nat.ofDigits? 10 s

def String.toInt32? (s : String) : Option Int32 := do
  if s.get 0 = '-' then
    let v ← (s.toSubstring.drop 1).toNat?';
    pure <| Numbers.Signed.ofInt (-v)
  else
    Numbers.Signed.ofInt <$> s.toSubstring.toNat?'

def String.toInt32! (s : String) : Int32 :=
  match s.toInt32? with
  | some v => v
  | none   => panic "Int32 expected"

def String.sanitise (s : String) : String :=
  s.foldl (fun acc c =>
    if c.toNat = 0 then acc ++ "\\0"
    else if c = '\n' then acc ++ "\\n"
    else if c = '\t' then acc ++ "\\t"
    else if c.toNat = 0x0B then acc ++ "\\v"
    else if c.toNat = 0x08 then acc ++ "\\b"
    else if c = '\r' then acc ++ "\\r"
    else if c.toNat = 0x0C then acc ++ "\\f"
    else if c.toNat = 0x07 then acc ++ "\\a"
    else if c = '\\' then acc ++ "\\\\"
    else if c = '\'' then acc ++ "\\'"
    else if c = '"' then acc ++ "\\\""
    else acc ++ c.toString
  ) ""

def UInt64.max (n m : UInt64) : UInt64 :=
  if n > m then n else m

def UInt64.toBytes (v : UInt64) : List UInt8 :=
  aux v 8
where aux (v : UInt64) (n : Nat) : List UInt8 :=
  if n = 0 then [] else (v % 256).toUInt8 :: aux (v / 256) (n - 1)

@[simp] theorem UInt32.toNat_ofUInt8 : UInt32.toNat (UInt8.toUInt32 x) = x.val := by
  cases x; case mk val =>
  cases val; case mk val isLt =>
  have : val < 4294967295 + 1 := Nat.le_trans isLt (by decide)
  simp [UInt8.size] at isLt
  simp only [toNat]
  apply Nat.mod_eq_of_lt this

instance : Coe UInt8 Char where
  coe b := ⟨UInt8.toUInt32 b, by
    rcases b with ⟨⟨x,h⟩⟩
    apply Or.inl
    simp
    apply Nat.lt_trans h (by decide)
  ⟩

def Char.toUInt8 (c : Char) (h : c.val.val < UInt8.size := by decide) : UInt8 :=
  ⟨c.val.val, h⟩

instance (h : c.val.val < UInt8.size := by decide) : CoeDep Char c UInt8 := ⟨c.toUInt8 h⟩

structure ThunkCache (a : Unit → α) where
  val : Thunk α
  h_val : val.get = a ()

def ThunkCache.new : ThunkCache a := ⟨Thunk.mk a, by simp [Thunk.get]⟩
instance : Inhabited (ThunkCache a) := ⟨.new⟩

-- def List.pmap (L : List α) (f : (a : α) → a ∈ L → β) : List β :=
  -- match L with
  -- | [] => []
  -- | x::xs => (f x (List.Mem.head _)) :: xs.pmap (fun a h => f a (List.Mem.tail _ h))

@[simp] theorem String.length_pushn (s : String) (c n)
  : (s.pushn c n).length = s.length + n := by
  induction n
  . simp [pushn, Nat.repeat]
  . simp [pushn, Nat.repeat, push, length]
    rw [Nat.add_succ, Nat.add_succ]
    congr

@[simp] theorem String.length_append (s1 s2 : String)
  : (s1 ++ s2).length = s1.length + s2.length := by
  simp [HAppend.hAppend, Append.append, append, length]

@[simp] theorem String.take_mk (L : List Char) (n)
  : (String.mk L).take n = String.mk (L.take n)
  := sorry

@[simp] theorem String.drop_mk (L : List Char) (n)
  : (String.mk L).drop n = String.mk (L.drop n)
  := sorry

@[simp] theorem String.length_take (s : String) (n)
  : (s.take n).length = min s.length n
  := by cases s; simp [length, Nat.min_comm]

@[simp] theorem String.length_drop (s : String) (n)
  : (s.drop n).length = s.length - n
  := by cases s; simp [length, Nat.min_comm]

theorem List.mem_zipWith (h : x ∈ List.zipWith f L1 L2)
  : ∃ y z, x = f y z ∧ y ∈ L1 ∧ z ∈ L2
  := by induction L1 generalizing x L2
        . simp at h
        . next ih =>
          cases L2 <;> simp at *
          cases h
          . subst_vars
            exact ⟨_, _, rfl, .inl rfl, .inl rfl⟩
          . have := ih (by assumption)
            rcases this with ⟨y,z,rfl,hy,hz⟩
            refine ⟨y,z, rfl, .inr hy, .inr hz⟩

theorem List.mem_take (h : x ∈ List.take n L)
  : x ∈ L
  := by induction n generalizing L <;> cases L <;> simp at *
        next ih _ _ =>
        cases h
        . apply Or.inl; assumption
        . apply Or.inr; apply ih; assumption

@[simp]
theorem List.length_join_replicate : (replicate n L).join.length = n * L.length := by
  induction n
  . simp
  . simp [Nat.succ_mul, Nat.add_comm]

def List.toMap [DecidableEq α] : List (α × β) → (α → Option β)
| []       => fun _ => none
| (a,b)::L => Function.update (toMap L) a (some b)

def List.toFn (lst : List α) : Fin lst.length → α :=
  fun i => lst.get i

def Std.HashMap.insert_multi [BEq α] [Hashable α]
    (self : Std.HashMap α (List β))
    (a : α)
    (b : β)
    : Std.HashMap α (List β) :=
  match self.find? a with
  | .none    => self.insert a [b]
  | .some bs => self.insert a (b :: bs)
