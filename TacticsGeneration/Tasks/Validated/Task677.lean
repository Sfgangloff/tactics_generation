import Batteries

open Std

def validityTriangle (a b c : Nat) : Bool :=
  let total := a + b + c
  if total == 180 then true else false

#guard validityTriangle 60 50 90 == false
#guard validityTriangle 45 75 60 == true
#guard validityTriangle 30 50 100 == true
