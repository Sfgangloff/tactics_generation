import Batteries
open Std

def insertOrdered (x : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [x]
  | y :: ys => if x ≤ y then x :: l else y :: insertOrdered x ys

def isort (l : List Nat) : List Nat :=
  l.foldl (fun acc x => insertOrdered x acc) []

def listGetD {α} (l : List α) (i : Nat) (d : α) : α :=
  match l, i with
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, i+1 => listGetD xs i d

def findPlatform (arr dep : List Nat) (n : Nat) : Nat := Id.run do
  let arrS := isort arr
  let depS := isort dep
  let mut plat_needed : Int := 1
  let mut result : Int := 1
  let mut i : Nat := 1
  let mut j : Nat := 0
  while decide (i < n) && decide (j < n) do
    let ai := listGetD arrS i 0
    let dj := listGetD depS j 0
    if ai ≤ dj then
      plat_needed := plat_needed + 1
      i := i + 1
    else
      plat_needed := plat_needed - 1
      j := j + 1
    if plat_needed > result then
      result := plat_needed
  return Int.toNat result

#guard findPlatform [900, 940, 950, 1100, 1500, 1800] [910, 1200, 1120, 1130, 1900, 2000] 6 = 3
#guard findPlatform [100,200,300,400] [700,800,900,1000] 4 = 4
#guard findPlatform [5,6,7,8] [4,3,2,1] 4 = 1
