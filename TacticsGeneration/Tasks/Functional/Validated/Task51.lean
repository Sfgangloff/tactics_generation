import Batteries

open Std

def checkEquilateral (x y z : Nat) : Bool :=
  if x == y && y == z then
    true
  else
    false

#guard checkEquilateral 6 8 12 == false
#guard checkEquilateral 6 6 12 == false
#guard checkEquilateral 6 6 6 == true
