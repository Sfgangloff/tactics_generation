import Batteries

open Std

def triangleArea (r : Int) : Int :=
  if r < 0 then
    -1
  else
    r * r

#guard triangleArea 0 = 0
#guard triangleArea (-1) = -1
#guard triangleArea 2 = 4
