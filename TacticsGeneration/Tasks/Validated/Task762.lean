import Batteries

open Std

def check_monthnumber_number (monthnum3 : Nat) : Bool :=
  if monthnum3 == 4 || monthnum3 == 6 || monthnum3 == 9 || monthnum3 == 11 then
    true
  else
    false

#guard check_monthnumber_number 6 == true
#guard check_monthnumber_number 2 == false
#guard check_monthnumber_number 12 == false
