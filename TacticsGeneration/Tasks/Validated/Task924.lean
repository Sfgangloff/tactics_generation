import Batteries

open Std

def maxOfTwo (x y : Int) : Int :=
  if x > y then x else y

#guard maxOfTwo 10 20 = 20
#guard maxOfTwo 19 15 = 19
#guard maxOfTwo (-10) (-20) = (-10)
