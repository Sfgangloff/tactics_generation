import Batteries

open Std

def checkIsosceles (x y z : Nat) : Bool :=
  (x == y) || (y == z) || (z == x)

#guard checkIsosceles 6 8 12 == false
#guard checkIsosceles 6 6 12 == true
#guard checkIsosceles 6 16 20 == false
