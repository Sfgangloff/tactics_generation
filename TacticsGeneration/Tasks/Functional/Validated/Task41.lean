import Batteries

open Std

def filterEvenNumbers (nums : List Int) : List Int :=
  nums.filter (fun x => x % 2 == 0)

#guard filterEvenNumbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] == [2, 4, 6, 8, 10]
#guard filterEvenNumbers [10, 20, 45, 67, 84, 93] == [10, 20, 84]
#guard filterEvenNumbers [5, 7, 9, 8, 6, 4, 3] == [8, 6, 4]
