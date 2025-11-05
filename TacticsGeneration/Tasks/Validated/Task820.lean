import Batteries

open Std

def checkMonthnumNumber (monthnum1 : Nat) : Bool :=
  if monthnum1 == 2 then true else false

#guard checkMonthnumNumber 2 == true
#guard checkMonthnumNumber 1 == false
#guard checkMonthnumNumber 3 == false
