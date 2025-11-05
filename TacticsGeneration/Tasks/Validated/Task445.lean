import Batteries

open Std

def indexMultiplication (test_tup1 : List (List Nat)) (test_tup2 : List (List Nat)) : List (List Nat) :=
  (List.zip test_tup1 test_tup2).map (fun (t1, t2) =>
    (List.zip t1 t2).map (fun (a, b) => a * b))

#guard indexMultiplication [[1, 3], [4, 5], [2, 9], [1, 10]] [[6, 7], [3, 9], [1, 1], [7, 3]] = [[6, 21], [12, 45], [2, 9], [7, 30]]
#guard indexMultiplication [[2, 4], [5, 6], [3, 10], [2, 11]] [[7, 8], [4, 10], [2, 2], [8, 4]] = [[14, 32], [20, 60], [6, 20], [16, 44]]
#guard indexMultiplication [[3, 5], [6, 7], [4, 11], [3, 12]] [[8, 9], [5, 11], [3, 3], [9, 5]] = [[24, 45], [30, 77], [12, 33], [27, 60]]
