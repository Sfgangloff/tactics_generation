import Batteries

open Std

def tetrahedralNumber (n : Nat) : Float :=
  (n * (n + 1) * (n + 2)).toFloat / 6.0

#guard tetrahedralNumber 5 == 35.0
#guard tetrahedralNumber 6 == 56.0
#guard tetrahedralNumber 7 == 84.0
