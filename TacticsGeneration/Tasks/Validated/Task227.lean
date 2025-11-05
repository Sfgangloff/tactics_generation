import Batteries

open Std

def minOfThree (a b c : Int) : Int :=
  if h1 : a ≤ b ∧ a ≤ c then
    a
  else if h2 : b ≤ a ∧ b ≤ c then
    b
  else
    c

#guard minOfThree 10 20 0 = 0
#guard minOfThree 19 15 18 = 15
#guard minOfThree (-10) (-20) (-30) = (-30)
