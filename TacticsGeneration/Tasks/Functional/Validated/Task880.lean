import Batteries

open Std

def Check_Solution (a b c : Int) : String :=
  let d := (b*b) - (4*a*c)
  if h : d > 0 then
    "2 solutions"
  else if h2 : d = 0 then
    "1 solution"
  else
    "No solutions"

#guard Check_Solution 2 5 2 = "2 solutions"
#guard Check_Solution 1 1 1 = "No solutions"
#guard Check_Solution 1 2 1 = "1 solution"
