import Batteries

open Std

def floorMin (A B N : Nat) : Nat :=
  let x := max (B - 1) N
  (A * x) / B

#guard floorMin 10 20 30 = 15
#guard floorMin 1 2 1 = 0
#guard floorMin 11 10 9 = 9
