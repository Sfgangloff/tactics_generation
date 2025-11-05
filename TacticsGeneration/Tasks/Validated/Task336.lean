import Batteries

open Std

def check_monthnum (monthname1 : String) : Bool :=
  if monthname1 == "February" then true else false

#guard check_monthnum "February" == true
#guard check_monthnum "January" == false
#guard check_monthnum "March" == false
