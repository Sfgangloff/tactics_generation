import Batteries

open Std

def Check_Solution (a b c : Int) : String :=
  if (2 * b * b) == (9 * a * c) then
    "Yes"
  else
    "No"

#guard Check_Solution 1 3 2 == "Yes"
#guard Check_Solution 1 2 3 == "No"
#guard Check_Solution 1 (-5) 6 == "No"
