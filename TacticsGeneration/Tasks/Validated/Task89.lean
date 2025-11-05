import Batteries

open Std

def closestNum (N : Nat) : Nat :=
  N - 1

#guard closestNum 11 == 10
#guard closestNum 7 == 6
#guard closestNum 12 == 11
