import Batteries

open Std

def moveFirst (test_list : List Nat) : List Nat :=
  let n := test_list.length
  test_list.drop (n - 1) ++ test_list.take (n - 1)

#guard moveFirst [1,2,3,4] = [4,1,2,3]
#guard moveFirst [0,1,2,3] = [3,0,1,2]
#guard moveFirst [9,8,7,1] = [1,9,8,7]
