import Batteries

open Std

def profitAmount (actualCost saleAmount : Nat) : Option Nat :=
  if actualCost > saleAmount then
    let amount := actualCost - saleAmount
    some amount
  else
    none

#guard profitAmount 1500 1200 = some 300
#guard profitAmount 100 200 = none
#guard profitAmount 2000 5000 = none
