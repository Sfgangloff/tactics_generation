import Batteries

open Std

def findAngle (a b : Nat) : Nat :=
  let c := 180 - (a + b)
  c

#guard findAngle 47 89 = 44
#guard findAngle 45 95 = 40
#guard findAngle 50 40 = 90
