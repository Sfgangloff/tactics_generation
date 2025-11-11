import Batteries

open Std

def apSum (a n d : Nat) : Nat :=
  (n * (2 * a + (n - 1) * d)) / 2

#guard apSum 1 5 2 = 25
#guard apSum 2 6 4 = 72
#guard apSum 1 4 5 = 34
