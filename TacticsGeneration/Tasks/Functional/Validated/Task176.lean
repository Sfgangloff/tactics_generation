import Batteries

open Std

def perimeterTriangle (a b c : Nat) : Nat :=
  let perimeter := a + b + c
  perimeter

#guard perimeterTriangle 10 20 30 = 60
#guard perimeterTriangle 3 4 5 = 12
#guard perimeterTriangle 25 35 45 = 105
