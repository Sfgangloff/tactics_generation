import Batteries

open Std

def sumList (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0

def cummulative_sum (test_list : List (List Nat)) : Nat :=
  (test_list.map sumList).foldl (· + ·) 0

#guard cummulative_sum [[1, 3], [5, 6, 7], [2, 6]] = 30
#guard cummulative_sum [[2, 4], [6, 7, 8], [3, 7]] = 37
#guard cummulative_sum [[3, 5], [7, 8, 9], [4, 8]] = 44
