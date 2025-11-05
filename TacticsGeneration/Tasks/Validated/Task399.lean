import Batteries

open Std

def bitwiseXor (test_tup1 : List Nat) (test_tup2 : List Nat) : List Nat :=
  (List.zip test_tup1 test_tup2).map (fun (a, b) => a ^^^ b)

#guard bitwiseXor [10, 4, 6, 9] [5, 2, 3, 3] == [15, 6, 5, 10]
#guard bitwiseXor [11, 5, 7, 10] [6, 3, 4, 4] == [13, 6, 3, 14]
#guard bitwiseXor [12, 6, 8, 11] [7, 4, 5, 6] == [11, 2, 13, 13]
