import Batteries

open Std

def rectanglePerimeter (l b : Nat) : Nat :=
  let perimeter := 2 * (l + b)
  perimeter

#guard rectanglePerimeter 10 20 = 60
#guard rectanglePerimeter 10 5 = 30
#guard rectanglePerimeter 4 2 = 12
