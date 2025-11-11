import Batteries

open Std

def countOddSquares (n m : Nat) : Nat :=
  Nat.sqrt m - Nat.sqrt (n - 1)

#guard countOddSquares 5 100 = 8
#guard countOddSquares 8 65 = 6
#guard countOddSquares 2 5 = 1
