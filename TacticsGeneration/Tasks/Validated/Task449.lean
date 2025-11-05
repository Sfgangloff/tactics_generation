import Batteries

open Std

def check_Triangle (x1 y1 x2 y2 x3 y3 : Int) : String :=
  let a := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2)
  if a == 0 then "No" else "Yes"

#guard check_Triangle 1 5 2 5 4 6 == "Yes"
#guard check_Triangle 1 1 1 4 1 5 == "No"
#guard check_Triangle 1 1 1 1 1 1 == "No"
