import Batteries

open Std

def largestTriangle (a b : Float) : Float :=
  if a < 0.0 || b < 0.0 then
    -1.0
  else
    (3.0 * Float.sqrt 3.0 * (a * a)) / (4.0 * b)

#guard largestTriangle 4.0 2.0 == 10.392304845413264
#guard largestTriangle 5.0 7.0 == 4.639421805988064
#guard largestTriangle 9.0 1.0 == 105.2220865598093
