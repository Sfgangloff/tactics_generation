import Batteries

open Std

def clearTuple (test_tup : List Nat) : List Nat :=
  let temp := test_tup
  let temp := ([] : List Nat)
  let test_tup := temp
  test_tup

#guard clearTuple [1, 5, 3, 6, 8] == []
#guard clearTuple [2, 1, 4, 5, 6] == []
#guard clearTuple [3, 2, 5, 6, 8] == []
