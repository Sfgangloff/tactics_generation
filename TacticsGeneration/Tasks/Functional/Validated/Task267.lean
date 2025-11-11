import Batteries

open Std

def square_Sum (n : Nat) : Nat :=
  n * (4 * n * n - 1) / 3

#guard square_Sum 2 = 10
#guard square_Sum 3 = 35
#guard square_Sum 4 = 84
