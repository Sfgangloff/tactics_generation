import Batteries

open Std

def volumeCube (l : Nat) : Nat :=
  let volume := l * l * l
  volume

#guard volumeCube 3 = 27
#guard volumeCube 2 = 8
#guard volumeCube 5 = 125
