import Batteries

open Std

def tupleModulo (test_tup1 test_tup2 : List Nat) : List Nat :=
  (List.zip test_tup1 test_tup2).map (fun (a, b) => a % b)

#guard tupleModulo [10, 4, 5, 6] [5, 6, 7, 5] = [0, 4, 5, 1]
#guard tupleModulo [11, 5, 6, 7] [6, 7, 8, 6] = [5, 5, 6, 1]
#guard tupleModulo [12, 6, 7, 8] [7, 8, 9, 7] = [5, 6, 7, 1]
