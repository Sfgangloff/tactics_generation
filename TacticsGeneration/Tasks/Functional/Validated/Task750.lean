import Batteries

open Std

def addTuple (test_list : List Nat) (test_tup : List Nat) : List Nat :=
  test_list ++ test_tup

#guard addTuple [5, 6, 7] [9, 10] == [5, 6, 7, 9, 10]
#guard addTuple [6, 7, 8] [10, 11] == [6, 7, 8, 10, 11]
#guard addTuple [7, 8, 9] [11, 12] == [7, 8, 9, 11, 12]
