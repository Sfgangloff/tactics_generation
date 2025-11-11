import Batteries

open Std

def check_Validity (a b c : Nat) : Bool :=
  if a + b <= c then false
  else if a + c <= b then false
  else if b + c <= a then false
  else true

#guard check_Validity 1 2 3 == false
#guard check_Validity 2 3 5 == false
#guard check_Validity 7 10 5 == true
