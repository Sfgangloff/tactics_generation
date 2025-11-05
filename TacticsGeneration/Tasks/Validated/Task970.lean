import Batteries

open Std

def min_of_two (x y : Int) : Int :=
  if h : x < y then x else y

#guard min_of_two 10 20 = 10
#guard min_of_two 19 15 = 15
#guard min_of_two (-10) (-20) = (-20)
