import Batteries

open Std

def alternateElements {α} (list1 : List α) : List α :=
  let rec go (take : Bool) (l : List α) : List α :=
    match l with
    | [] => []
    | x :: xs =>
      if take then x :: go false xs else go true xs
  go true list1

#guard alternateElements ["red", "black", "white", "green", "orange"] == ["red", "white", "orange"]
#guard alternateElements ([2, 0, 3, 4, 0, 2, 8, 3, 4, 2] : List Nat) == [2, 3, 0, 8, 4]
#guard alternateElements ([1,2,3,4,5,6,7,8,9,10] : List Nat) == [1,3,5,7,9]
