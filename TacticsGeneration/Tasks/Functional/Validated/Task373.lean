import Batteries

open Std

def volumeCuboid (l w h : Nat) : Nat :=
  let volume := l * w * h
  volume

#guard volumeCuboid 1 2 3 = 6
#guard volumeCuboid 5 7 9 = 315
#guard volumeCuboid 10 15 21 = 3150
