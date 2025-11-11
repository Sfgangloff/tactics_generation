import Batteries

open Std

def findMissing (ar : List Nat) (N : Nat) : Int := Id.run do
  
  
  
  
  let mut l : Nat := 0
  let mut r : Nat := N - 1
  while Nat.ble l r do
    let mid := (l + r) / 2
    let aMid := ar.getD mid 0
    if (aMid ≠ mid + 1) ∧ (ar.getD (mid - 1) 0 = mid) then
      return (Int.ofNat (mid + 1))
    else if aMid ≠ mid + 1 then
      r := mid - 1
    else
      l := mid + 1
  return (-1)

#guard findMissing [1, 2, 3, 5] 4 = (4 : Int)
#guard findMissing [1, 3, 4, 5] 4 = (2 : Int)
#guard findMissing [1, 2, 3, 5, 6, 7] 5 = (4 : Int)
