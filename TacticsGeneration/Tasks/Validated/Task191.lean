import Batteries

open Std

def checkMonthnumber (monthname3 : String) : Bool :=
  if monthname3 == "April" || monthname3 == "June" || monthname3 == "September" || monthname3 == "November" then
    true
  else
    false

#guard checkMonthnumber "February" == false
#guard checkMonthnumber "June" == true
#guard checkMonthnumber "April" == true
