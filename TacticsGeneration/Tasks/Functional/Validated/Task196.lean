import Batteries

open Std

def removeTuples (testList : List (List Nat)) (K : Nat) : List (List Nat) :=
  testList.filter (fun ele => ele.length != K)

#guard removeTuples [[4, 5], [4], [8, 6, 7], [1], [3, 4, 6, 7]] 1 = [[4, 5], [8, 6, 7], [3, 4, 6, 7]]
#guard removeTuples [[4, 5], [4, 5], [6, 7], [1, 2, 3], [3, 4, 6, 7]] 2 = [[1, 2, 3], [3, 4, 6, 7]]
#guard removeTuples [[1, 4, 4], [4, 3], [8, 6, 7], [1], [3, 6, 7]] 3 = [[4, 3], [1]]
