import Batteries

open Std

def specifiedElement (nums : List (List Nat)) (N : Nat) : List Nat :=
  nums.map (fun i => i.getD N 0)

#guard specifiedElement [[1, 2, 3, 2], [4, 5, 6, 2], [7, 1, 9, 5]] 0 == [1, 4, 7]
#guard specifiedElement [[1, 2, 3, 2], [4, 5, 6, 2], [7, 1, 9, 5]] 2 == [3, 6, 9]
#guard specifiedElement [[1, 2, 3, 2], [4, 5, 6, 2], [7, 1, 9, 5]] 3 == [2, 2, 5]
