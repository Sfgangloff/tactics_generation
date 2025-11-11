import Batteries

open Std

def Split (list : List Nat) : List Nat :=
  list.filter (fun i => i % 2 != 0)

#guard Split [1,2,3,4,5,6] == [1,3,5]
#guard Split [10,11,12,13] == [11,13]
#guard Split [7,8,9,1] == [7,9,1]
