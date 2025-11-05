import Batteries

open Std

def square_Sum (n : Nat) : Nat :=
  (2 * n * (n + 1) * (2 * n + 1)) / 3

#guard square_Sum 2 = 20
#guard square_Sum 3 = 56
#guard square_Sum 4 = 120
