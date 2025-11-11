import Batteries
open Std

def findFirstOccurrence (A : List Nat) (x : Nat) : Int := Id.run do
  let mut left : Int := 0
  let mut right : Int := (Int.ofNat A.length) - 1
  let mut result : Int := -1
  while left <= right do
    let mid : Int := (left + right) / 2
    let midNat : Nat := Int.toNat mid
    if h : midNat < A.length then
      let midFin : Fin A.length := ⟨midNat, h⟩
      let midVal : Nat := A.get midFin
      if x == midVal then
        result := mid
        right := mid - 1
      else if x < midVal then
        right := mid - 1
      else
        left := mid + 1
    else
      
      left := right + 1
  return result

#guard findFirstOccurrence [2, 5, 5, 5, 6, 6, 8, 9, 9, 9] 5 = 1
#guard findFirstOccurrence [2, 3, 5, 5, 6, 6, 8, 9, 9, 9] 5 = 2
#guard findFirstOccurrence [2, 4, 1, 5, 6, 6, 8, 9, 9, 9] 6 = 4
