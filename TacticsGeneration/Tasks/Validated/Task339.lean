import Batteries

open Std

def findDivisor (x y : Nat) : Nat :=
  if x == y then y else 2

#guard findDivisor 2 2 = 2
#guard findDivisor 2 5 = 2
#guard findDivisor 5 10 = 2
