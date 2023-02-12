import Std

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

def Nat.ofDigits? (base : Nat) (s : String) : Option Nat :=
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
