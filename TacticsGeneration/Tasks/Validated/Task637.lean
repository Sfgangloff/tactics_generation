import Batteries

open Std

def noprofit_noloss (actual_cost sale_amount : Nat) : Bool :=
  if sale_amount == actual_cost then true else false

#guard noprofit_noloss 1500 1200 == false
#guard noprofit_noloss 100 100 == true
#guard noprofit_noloss 2000 5000 == false
