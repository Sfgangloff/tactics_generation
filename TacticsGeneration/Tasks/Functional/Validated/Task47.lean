import Batteries
open Std

def compute_Last_Digit (A B : Nat) : Nat := Id.run do
  let mut variable_ := 1
  if A == B then
    return 1
  else if decide ((B - A) ≥ 5) then
    return 0
  else
    for i in [A+1 : B+1] do
      variable_ := (variable_ * (i % 10)) % 10
    return variable_ % 10

#guard compute_Last_Digit 2 4 = 2
#guard compute_Last_Digit 6 8 = 6
#guard compute_Last_Digit 1 2 = 2

#guard compute_Last_Digit 3 7 = 0
#guard compute_Last_Digit 20 23 = 6
#guard compute_Last_Digit 1021 1024 = 4
