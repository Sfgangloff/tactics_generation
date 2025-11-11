import Batteries

open Std

def inAsciiRange (c : Char) (lo hi : Char) : Bool :=
  let n := c.toNat
  let l := lo.toNat
  let h := hi.toNat
  Nat.ble l n && Nat.ble n h

def asciiIsAlpha (c : Char) : Bool :=
  inAsciiRange c 'a' 'z' || inAsciiRange c 'A' 'Z'

def asciiIsDigit (c : Char) : Bool :=
  inAsciiRange c '0' '9'

def countAlphaDigSpl (s : String) : Nat × Nat × Nat := Id.run do
  let mut alphabets := 0
  let mut digits := 0
  let mut special := 0
  for c in s.data do
    if asciiIsAlpha c then
      alphabets := alphabets + 1
    else if asciiIsDigit c then
      digits := digits + 1
    else
      special := special + 1
  return (alphabets, digits, special)

#guard countAlphaDigSpl "abc!@#123" = (3,3,3)
#guard countAlphaDigSpl "dgsuy@#$%&1255" = (5,4,5)
#guard countAlphaDigSpl "fjdsif627348#%$^&" = (6,6,5)
