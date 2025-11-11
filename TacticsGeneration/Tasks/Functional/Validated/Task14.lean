import Batteries

open Std

def findVolume (l b h : Nat) : Nat :=
  (l * b * h) / 2

#guard findVolume 10 8 6 == 240
#guard findVolume 3 2 2 == 6
#guard findVolume 1 2 1 == 1
