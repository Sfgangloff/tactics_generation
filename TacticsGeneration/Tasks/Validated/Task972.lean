import Batteries

open Std

def concatenateNested (test_tup1 test_tup2 : List Nat) : List Nat :=
  let res := test_tup1 ++ test_tup2
  res

#guard concatenateNested [3, 4] [5, 6] = [3, 4, 5, 6]
#guard concatenateNested [1, 2] [3, 4] = [1, 2, 3, 4]
#guard concatenateNested [4, 5] [6, 8] = [4, 5, 6, 8]
