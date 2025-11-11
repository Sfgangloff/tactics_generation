import Batteries

open Std

def check_isosceles (x y z : Nat) : Bool :=
  if (! (x == y)) && (! (y == z)) && (! (z == x)) then
    true
  else
    false

#guard check_isosceles 6 8 12 == true
#guard check_isosceles 6 6 12 == false
#guard check_isosceles 6 15 20 == true
