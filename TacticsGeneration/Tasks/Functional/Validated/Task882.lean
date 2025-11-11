import Batteries

open Std

def parallelogramPerimeter (b h : Nat) : Nat :=
  2 * (b * h)

#guard parallelogramPerimeter 10 20 = 400
#guard parallelogramPerimeter 15 20 = 600
#guard parallelogramPerimeter 8 9 = 144
