import Batteries

open Std

def Check_Solution (a b c : Int) : String :=
  if b == 0 then "Yes" else "No"

#guard Check_Solution 2 0 (-1) == "Yes"
#guard Check_Solution 1 (-5) 6 == "No"
#guard Check_Solution 2 0 2 == "Yes"
