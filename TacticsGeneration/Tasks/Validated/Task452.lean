import Batteries

open Std

def lossAmount (actual_cost sale_amount : Nat) : Option Nat :=
  if sale_amount > actual_cost then
    some (sale_amount - actual_cost)
  else
    none

#guard lossAmount 1500 1200 == none
#guard lossAmount 100 200 == some 100
#guard lossAmount 2000 5000 == some 3000
