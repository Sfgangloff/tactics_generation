import Batteries

open Std

def filterOddnumbers (nums : List Nat) : List Nat :=
  nums.filter (fun x => x % 2 != 0)

#guard filterOddnumbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] == [1,3,5,7,9]
#guard filterOddnumbers [10,20,45,67,84,93] == [45,67,93]
#guard filterOddnumbers [5,7,9,8,6,4,3] == [5,7,9,3]
