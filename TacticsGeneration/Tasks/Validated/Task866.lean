import Batteries

open Std

def checkMonthnumb (monthname2 : String) : Bool :=
  if monthname2 == "January" || monthname2 == "March" || monthname2 == "May" || monthname2 == "July" || monthname2 == "Augest" || monthname2 == "October" || monthname2 == "December" then
    true
  else
    false

#guard checkMonthnumb "February" == false
#guard checkMonthnumb "January" == true
#guard checkMonthnumb "March" == true
