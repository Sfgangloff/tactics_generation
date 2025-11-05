import Batteries

open Std

def findRectNum (n : Nat) : Nat :=
  n * (n + 1)

#guard findRectNum 4 == 20
#guard findRectNum 5 == 30
#guard findRectNum 6 == 42
