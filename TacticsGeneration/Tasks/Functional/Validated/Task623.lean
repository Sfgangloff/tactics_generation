import Batteries

open Std

def nthNums (nums : List Nat) (n : Nat) : List Nat :=
  nums.map (fun x => x ^ n)

#guard nthNums [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 2 == [1, 4, 9, 16, 25, 36, 49, 64, 81, 100]
#guard nthNums [10, 20, 30] 3 == [1000, 8000, 27000]
#guard nthNums [12, 15] 5 == [248832, 759375]
