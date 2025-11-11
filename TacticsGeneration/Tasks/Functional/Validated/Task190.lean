import Batteries

open Std

def count_Intgral_Points (x1 y1 x2 y2 : Int) : Int :=
  (y2 - y1 - 1) * (x2 - x1 - 1)

#guard count_Intgral_Points 1 1 4 4 = 4
#guard count_Intgral_Points 1 2 1 2 = 1
#guard count_Intgral_Points 4 2 6 4 = 1
