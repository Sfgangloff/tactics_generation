import Batteries

open Std

def next_Perfect_Square (N : Nat) : Nat :=
  let nextN := Nat.sqrt N + 1
  nextN * nextN

#guard next_Perfect_Square 35 = 36
#guard next_Perfect_Square 6 = 9
#guard next_Perfect_Square 9 = 16
