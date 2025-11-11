import Batteries

open Std

def check_monthnumb_number (monthnum2 : Nat) : Bool :=
  if monthnum2 == 1 || monthnum2 == 3 || monthnum2 == 5 || monthnum2 == 7 || monthnum2 == 8 || monthnum2 == 10 || monthnum2 == 12 then
    true
  else
    false

#guard check_monthnumb_number 5 == true
#guard check_monthnumb_number 2 == false
#guard check_monthnumb_number 6 == false
