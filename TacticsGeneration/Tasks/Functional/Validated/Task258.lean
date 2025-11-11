import Batteries

open Std

def countOdd (arrayNums : List Int) : Nat :=
  (arrayNums.filter (fun x => !(x % 2 == 0))).length

#guard countOdd [1, 2, 3, 5, 7, 8, 10] = 4
#guard countOdd [10, 15, 14, 13, -18, 12, -20] = 2
#guard countOdd [1, 2, 4, 8, 9] = 2
