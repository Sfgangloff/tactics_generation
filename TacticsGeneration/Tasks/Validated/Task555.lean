import Batteries

open Std

def difference (n : Nat) : Nat :=
  let S := (n * (n + 1)) / 2
  let res := S * (S - 1)
  res

#guard difference 3 = 30
#guard difference 5 = 210
#guard difference 2 = 6
