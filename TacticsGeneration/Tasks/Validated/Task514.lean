import Batteries

open Std

def sumElements (test_tup : List Nat) : Nat :=
  let res := test_tup.foldl (fun acc x => acc + x) 0
  res

#guard sumElements [7, 8, 9, 1, 10, 7] = 42
#guard sumElements [1, 2, 3, 4, 5, 6] = 21
#guard sumElements [11, 12, 13, 45, 14] = 95
