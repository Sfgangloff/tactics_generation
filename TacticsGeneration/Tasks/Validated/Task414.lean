import Batteries
open Std

private def getAt (xs : List Nat) (i : Nat) (default : Nat) : Nat :=
  match xs.drop i with
  | [] => default
  | a :: _ => a

def overlapping (list1 list2 : List Nat) : Bool := Id.run do
  let mut c := 0
  let mut d := 0
  for _ in list1 do
    c := c + 1
  for _ in list2 do
    d := d + 1
  for i in [0:c] do
    for j in [0:d] do
      let a := getAt list1 i 0
      let b := getAt list2 j 0
      if a == b then
        return true
  return false

#guard overlapping [1,2,3,4,5] [6,7,8,9] == false
#guard overlapping [1,2,3] [4,5,6] == false
#guard overlapping [1,4,5] [1,4,5] == true
