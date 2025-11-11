import Batteries

open Std

def surfaceArea (b s : Nat) : Nat :=
  2 * b * s + b ^ 2

#guard surfaceArea 3 4 = 33
#guard surfaceArea 4 5 = 56
#guard surfaceArea 1 2 = 5
