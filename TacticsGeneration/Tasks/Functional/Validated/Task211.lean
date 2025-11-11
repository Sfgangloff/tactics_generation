import Batteries

open Std

def countNum (n : Nat) : Nat :=
  if n == 1 then
    1
  else
    2 ^ (n - 2)

#guard countNum 2 = 1
#guard countNum 3 = 2
#guard countNum 1 = 1
