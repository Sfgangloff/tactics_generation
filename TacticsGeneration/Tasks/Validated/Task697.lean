import Batteries

open Std

def count_even (array_nums : List Int) : Nat :=
  (array_nums.filter (fun x => x % 2 == 0)).length

#guard count_even [1, 2, 3, 5, 7, 8, 9, 10] == 3
#guard count_even [10,15,14,13,-18,12,-20] == 5
#guard count_even [1, 2, 4, 8, 9] == 3
