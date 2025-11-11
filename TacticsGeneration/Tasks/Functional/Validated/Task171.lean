import Batteries

open Std

def perimeter_pentagon (a : Nat) : Nat :=
  5 * a

#guard perimeter_pentagon 5 = 25
#guard perimeter_pentagon 10 = 50
#guard perimeter_pentagon 15 = 75
