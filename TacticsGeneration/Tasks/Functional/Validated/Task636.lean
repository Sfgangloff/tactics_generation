import Batteries

open Std

def Check_Solution (a b c : Int) : String :=
  if a == c then "Yes" else "No"

#guard Check_Solution 2 0 2 == "Yes"
#guard Check_Solution 2 (-5) 2 == "Yes"
#guard Check_Solution 1 2 3 == "No"
