import Batteries

open Std

def slope (x1 y1 x2 y2 : Int) : Float :=
  (Float.ofInt (y2 - y1)) / (Float.ofInt (x2 - x1))

#guard slope 4 2 2 5 == (-1.5)
#guard slope 2 4 4 6 == 1
#guard slope 1 2 4 2 == 0
