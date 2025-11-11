import Batteries
open Std

def findTuples (testList : List (List Nat)) (k : Nat) : String :=
  let res := testList.filter (fun sub => sub.all (fun ele => ele % k == 0))
  toString res

#guard findTuples [[6, 24, 12], [7, 9, 6], [12, 18, 21]] 6 == "[[6, 24, 12]]"
#guard findTuples [[5, 25, 30], [4, 2, 3], [7, 8, 9]] 5 == "[[5, 25, 30]]"
#guard findTuples [[7, 9, 16], [8, 16, 4], [19, 17, 18]] 4 == "[[8, 16, 4]]"
