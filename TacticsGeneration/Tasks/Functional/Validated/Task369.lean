import Batteries

open Std

def lateralsurface_cuboid (l w h : Nat) : Nat :=
  let LSA := 2 * h * (l + w)
  LSA

#guard lateralsurface_cuboid 8 5 6 = 156
#guard lateralsurface_cuboid 7 9 10 = 320
#guard lateralsurface_cuboid 10 20 30 = 1800
