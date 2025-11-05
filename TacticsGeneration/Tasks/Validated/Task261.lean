import Batteries

open Std

def divisionElements (test_tup1 : List Nat) (test_tup2 : List Nat) : List Nat :=
  match test_tup1, test_tup2 with
  | x::xs, y::ys => (x / y) :: divisionElements xs ys
  | _, _ => []

#guard divisionElements [10, 4, 6, 9] [5, 2, 3, 3] == [2, 2, 2, 3]
#guard divisionElements [12, 6, 8, 16] [6, 3, 4, 4] == [2, 2, 2, 4]
#guard divisionElements [20, 14, 36, 18] [5, 7, 6, 9] == [4, 2, 6, 2]
