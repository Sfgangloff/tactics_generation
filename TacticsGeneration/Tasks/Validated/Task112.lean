import Batteries

open Std

def perimeter (diameter height : Nat) : Nat :=
  2 * (diameter + height)

#guard perimeter 2 4 == 12
#guard perimeter 1 2 == 6
#guard perimeter 3 1 == 8
