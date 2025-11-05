import Batteries

open Std

def squareNums (nums : List Nat) : List Nat := nums.map (fun x => x ^ 2)

#guard squareNums [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] == [1, 4, 9, 16, 25, 36, 49, 64, 81, 100]
#guard squareNums [10, 20, 30] == [100, 400, 900]
#guard squareNums [12, 15] == [144, 225]
