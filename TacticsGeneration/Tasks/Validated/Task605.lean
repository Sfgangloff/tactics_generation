import Batteries

open Std

def primeNum (num : Int) : Bool := Id.run do
  if num >= 1 then
    let halfNat : Nat := Int.toNat (num / 2)
    for i in [2 : halfNat] do
      if num % (Int.ofNat i) == 0 then
        return false
      else
        return true
    return false
  else
    return false

#guard primeNum 13 == true
#guard primeNum 7 == true
#guard primeNum (-1010) == false
