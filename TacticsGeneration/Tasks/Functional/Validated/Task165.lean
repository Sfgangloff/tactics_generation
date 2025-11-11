import Batteries

open Std

def countCharPosition (str1 : String) : Nat := Id.run do
  let ordA : Int := Int.ofNat (Char.toNat 'A')
  let ordLowerA : Int := Int.ofNat (Char.toNat 'a')
  let mut count : Nat := 0
  let mut i : Nat := 0
  for c in str1.data do
    let ci : Int := Int.ofNat (Char.toNat c)
    let iI : Int := Int.ofNat i
    if iI == ci - ordA || iI == ci - ordLowerA then
      count := count + 1
    i := i + 1
  return count

#guard countCharPosition "xbcefg" = 2
#guard countCharPosition "ABcED" = 3
#guard countCharPosition "AbgdeF" = 5
