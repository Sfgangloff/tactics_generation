import Batteries

open Std

def squarePerimeter (a : Nat) : Nat :=
  4 * a

#guard squarePerimeter 10 == 40
#guard squarePerimeter 5 == 20
#guard squarePerimeter 4 == 16
