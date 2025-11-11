import Batteries

open Std

def andTuples (test_tup1 : List Nat) (test_tup2 : List Nat) : List Nat :=
  (List.zip test_tup1 test_tup2).map (fun (a, b) => a &&& b)

#guard andTuples [10, 4, 6, 9] [5, 2, 3, 3] == [0, 0, 2, 1]
#guard andTuples [1, 2, 3, 4] [5, 6, 7, 8] == [1, 2, 3, 0]
#guard andTuples [8, 9, 11, 12] [7, 13, 14, 17] == [0, 9, 10, 0]
