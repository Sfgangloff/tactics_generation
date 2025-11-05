import Batteries

open Std

def reverse_Array_Upto_K (input : List Nat) (k : Nat) : List Nat :=
  let first := input.take k
  let rest := input.drop k
  first.reverse ++ rest

#guard reverse_Array_Upto_K [1, 2, 3, 4, 5, 6] 4 = [4, 3, 2, 1, 5, 6]
#guard reverse_Array_Upto_K [4, 5, 6, 7] 2 = [5, 4, 6, 7]
#guard reverse_Array_Upto_K [9, 8, 7, 6, 5] 3 = [7, 8, 9, 6, 5]
