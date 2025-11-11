import Batteries

open Std

def diameterCircle (r : Nat) : Nat :=
  let diameter := 2 * r
  diameter

#guard diameterCircle 10 = 20
#guard diameterCircle 40 = 80
#guard diameterCircle 15 = 30
