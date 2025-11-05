import Batteries

open Std

def binaryToInteger (test_tup : List Nat) : String :=
  let n := test_tup.foldl (fun acc ele => acc * 2 + ele) 0
  toString n

#guard binaryToInteger [1, 1, 0, 1, 0, 0, 1] = "105"
#guard binaryToInteger [0, 1, 1, 0, 0, 1, 0, 1] = "101"
#guard binaryToInteger [1, 1, 0, 1, 0, 1] = "53"
