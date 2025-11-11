import Batteries

open Std

def findStarNum (n : Nat) : Nat :=
  (6 * n * (n - 1) + 1)

#guard findStarNum 3 = 37
#guard findStarNum 4 = 73
#guard findStarNum 5 = 121
