import Batteries

open Std

partial def smallest_missing (A : List Nat) (left_element right_element : Int) : Nat :=
  if left_element > right_element then
    Int.toNat left_element
  else
    let mid : Int := left_element + (right_element - left_element) / (2 : Int)
    let midNat := Int.toNat mid
    let aMid := A.getD midNat 0
    if aMid == midNat then
      smallest_missing A (mid + 1) right_element
    else
      smallest_missing A left_element (mid - 1)

#guard smallest_missing [0, 1, 2, 3, 4, 5, 6] (0 : Int) (6 : Int) == 7
#guard smallest_missing [0, 1, 2, 6, 9, 11, 15] (0 : Int) (6 : Int) == 3
#guard smallest_missing [1, 2, 3, 4, 6, 9, 11, 15] (0 : Int) (7 : Int) == 0
