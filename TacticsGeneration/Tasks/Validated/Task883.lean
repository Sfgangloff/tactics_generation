import Batteries

open Std

def divOfNums (nums : List Nat) (m n : Nat) : List Nat :=
  nums.filter (fun x => (x % m == 0) && (x % n == 0))

#guard divOfNums [19, 65, 57, 39, 152, 639, 121, 44, 90, 190] 2 4 = [152, 44]
#guard divOfNums [1, 2, 3, 5, 7, 8, 10] 2 5 = [10]
#guard divOfNums [10, 15, 14, 13, 18, 12, 20] 10 5 = [10, 20]
