import Batteries

open Std

def hexagonalNum (n : Nat) : Nat :=
  n * (2*n - 1)

#guard hexagonalNum 10 = 190
#guard hexagonalNum 5 = 45
#guard hexagonalNum 7 = 91
