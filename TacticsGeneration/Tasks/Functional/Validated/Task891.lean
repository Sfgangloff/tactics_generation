import Batteries

open Std

def sameLength (A B : Nat) : Bool := Id.run do
  let mut a := A
  let mut b := B
  while a > 0 && b > 0 do
    a := a / 10
    b := b / 10
  return a == 0 && b == 0

#guard sameLength 12 1 == false
#guard sameLength 2 2 == true
#guard sameLength 10 20 == true
