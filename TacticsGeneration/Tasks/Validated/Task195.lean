import Batteries
open Std

def listGetD {α} (l : List α) (i : Nat) (d : α) : α :=
  match l.drop i with
  | [] => d
  | h :: _ => h

def first (arr : List Nat) (x : Nat) (n : Nat) : Int := Id.run do
  
  let mut low : Int := 0
  let mut high : Int := (Int.ofNat n) - 1
  let mut res : Int := -1
  while _h : low ≤ high do
    let mid : Int := (low + high) / 2
    let midNat : Nat := Int.toNat mid
    let midVal : Nat := listGetD arr midNat 0
    if midVal > x then
      high := mid - 1
    else if midVal < x then
      low := mid + 1
    else
      res := mid
      high := mid - 1
  return res

#guard first [1,2,3,4,5,6,6] 6 6 = 5
#guard first [1,2,2,2,3,2,2,4,2] 2 9 = 1
#guard first [1,2,3] 1 3 = 0
