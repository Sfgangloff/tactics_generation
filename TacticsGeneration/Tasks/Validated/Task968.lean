import Batteries

open Std

def floorMax (A B N : Nat) : Nat :=
  let x := min (B - 1) N
  Nat.div (A * x) B

#guard floorMax 11 10 9 = 9
#guard floorMax 5 7 4 = 2
#guard floorMax 2 2 1 = 1
