import Batteries

open Std

def lateralsurfaceCube (l : Nat) : Nat :=
  4 * (l * l)

#guard lateralsurfaceCube 5 = 100
#guard lateralsurfaceCube 9 = 324
#guard lateralsurfaceCube 10 = 400
