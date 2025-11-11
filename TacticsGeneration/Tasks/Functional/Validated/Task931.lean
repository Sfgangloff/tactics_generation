import Batteries

open Std

def sumSeries (number : Nat) : Nat :=
  let half := (number * (number + 1)) / 2
  half * half

#guard sumSeries 7 = 784
#guard sumSeries 5 = 225
#guard sumSeries 15 = 14400
