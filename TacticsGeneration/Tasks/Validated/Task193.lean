import Batteries

open Std

def removeTuple (testTup : List Nat) : HashSet Nat :=
  HashSet.ofList testTup

#guard removeTuple [1, 3, 5, 2, 3, 5, 1, 1, 3] == Std.HashSet.ofList [1, 2, 3, 5]
#guard removeTuple [2, 3, 4, 4, 5, 6, 6, 7, 8, 8] == Std.HashSet.ofList [2, 3, 4, 5, 6, 7, 8]
#guard removeTuple [11, 12, 13, 11, 11, 12, 14, 13] == Std.HashSet.ofList [11, 12, 13, 14]
