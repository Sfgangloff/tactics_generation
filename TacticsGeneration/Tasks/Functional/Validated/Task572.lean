import Batteries

open Std

def listCount (xs : List Nat) (x : Nat) : Nat :=
  xs.foldl (fun acc y => acc + (if y == x then 1 else 0)) 0

def twoUniqueNums (nums : List Nat) : List Nat :=
  nums.filter (fun i => listCount nums i == 1)

#guard twoUniqueNums [1,2,3,2,3,4,5] == [1, 4, 5]
#guard twoUniqueNums [1,2,3,2,4,5] == [1, 3, 4, 5]
#guard twoUniqueNums [1,2,3,4,5] == [1, 2, 3, 4, 5]
