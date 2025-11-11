import Batteries

open Std

def sum_Odd (n : Nat) : Nat :=
  let terms := (n + 1) / 2
  let sum1 := terms * terms
  sum1

def sum_in_Range (l r : Nat) : Nat :=
  sum_Odd r - sum_Odd (l - 1)

#guard sum_in_Range 2 5 = 8
#guard sum_in_Range 5 7 = 12
#guard sum_in_Range 7 13 = 40
