import Batteries

open Std

def sumNums (x y m n : Nat) : Nat :=
  let s := x + y
  if m ≤ s ∧ s < n then 20 else s

#guard sumNums 2 10 11 20 = 20
#guard sumNums 15 17 1 10 = 32
#guard sumNums 10 15 5 30 = 20
