import Batteries

open Std

def lcopy (xs : List Nat) : List Nat :=
  
  xs

#guard lcopy [1, 2, 3] = [1, 2, 3]
#guard lcopy [4, 8, 2, 10, 15, 18] = [4, 8, 2, 10, 15, 18]
#guard lcopy [4, 5, 6] = [4, 5, 6]
