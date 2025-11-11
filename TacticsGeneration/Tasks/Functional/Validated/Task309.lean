import Batteries

open Std

def maximum (a b : Int) : Int :=
  if a >= b then a else b

#guard maximum 5 10 = 10
#guard maximum (-1) (-2) = -1
#guard maximum 9 7 = 9
