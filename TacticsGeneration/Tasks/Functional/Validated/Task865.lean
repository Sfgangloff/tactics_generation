import Batteries

open Std

def ntimes_list (nums : List Nat) (n : Nat) : List Nat :=
  nums.map (fun x => n * x)

#guard ntimes_list [1, 2, 3, 4, 5, 6, 7] 3 == [3, 6, 9, 12, 15, 18, 21]
#guard ntimes_list [1, 2, 3, 4, 5, 6, 7] 4 == [4, 8, 12, 16, 20, 24, 28]
#guard ntimes_list [1, 2, 3, 4, 5, 6, 7] 10 == [10, 20, 30, 40, 50, 60, 70]
