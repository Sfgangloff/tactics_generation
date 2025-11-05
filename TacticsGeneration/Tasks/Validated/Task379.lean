import Batteries

open Std

def surfacearea_cuboid (l w h : Nat) : Nat :=
  2 * (l * w + l * h + w * h)

#guard surfacearea_cuboid 1 2 3 = 22
#guard surfacearea_cuboid 5 7 9 = 286
#guard surfacearea_cuboid 10 15 21 = 1350
