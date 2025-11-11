import Batteries

open Std

def seriesSum (number : Nat) : Nat :=
  let total := 0
  let total := (number * (number + 1) * (2 * number + 1)) / 6
  total

#guard seriesSum 6 = 91
#guard seriesSum 7 = 140
#guard seriesSum 12 = 650
