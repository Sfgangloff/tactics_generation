import Batteries

open Std

def getCarol (n : Nat) : Nat :=
  let result := (2 ^ n) - 1
  result * result - 2

#guard getCarol 2 = 7
#guard getCarol 4 = 223
#guard getCarol 5 = 959
