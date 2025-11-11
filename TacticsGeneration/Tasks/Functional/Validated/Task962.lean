import Batteries

open Std

def sum_Natural (n : Nat) : Nat :=
  n * (n + 1)

def sum_Even (l r : Nat) : Nat :=
  sum_Natural (r / 2) - sum_Natural ((l - 1) / 2)

#guard sum_Even 2 5 = 6
#guard sum_Even 3 8 = 18
#guard sum_Even 4 6 = 10
