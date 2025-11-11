import Batteries

open Std

def cubeNums (nums : List Nat) : List Nat :=
  nums.map (fun x => x ^ 3)

#guard cubeNums [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] == [1, 8, 27, 64, 125, 216, 343, 512, 729, 1000]
#guard cubeNums [10, 20, 30] == [1000, 8000, 27000]
#guard cubeNums [12, 15] == [1728, 3375]
