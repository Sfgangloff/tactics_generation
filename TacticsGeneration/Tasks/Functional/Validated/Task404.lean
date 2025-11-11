import Batteries

open Std

def minimum (a b : Int) : Int :=
  if a <= b then a else b

#guard minimum 1 2 = 1
#guard minimum (-5) (-4) = (-5)
#guard minimum 0 0 = 0
