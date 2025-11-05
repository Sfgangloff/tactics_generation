import Batteries

open Std

def addPairwise (test_tup : List Nat) : List Nat :=
  let rec go (l : List Nat) : List Nat :=
    match l with
    | x :: y :: rest => (x + y) :: go (y :: rest)
    | _ => []
  go test_tup

#guard addPairwise [1, 5, 7, 8, 10] = [6, 12, 15, 18]
#guard addPairwise [2, 6, 8, 9, 11] = [8, 14, 17, 20]
#guard addPairwise [3, 7, 9, 10, 12] = [10, 16, 19, 22]
