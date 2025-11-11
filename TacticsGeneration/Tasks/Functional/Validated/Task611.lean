import Batteries

open Std

def maxOfNth (testList : List (List Nat)) (N : Nat) : Nat :=
  let vals := testList.map (fun sub => sub.getD N 0)
  vals.foldl (fun acc x => if x > acc then x else acc) 0

#guard maxOfNth [[5, 6, 7], [1, 3, 5], [8, 9, 19]] 2 = 19
#guard maxOfNth [[6, 7, 8], [2, 4, 6], [9, 10, 20]] 1 = 10
#guard maxOfNth [[7, 8, 9], [3, 5, 7], [10, 11, 21]] 1 = 11
