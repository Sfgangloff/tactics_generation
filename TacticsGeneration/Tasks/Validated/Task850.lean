import Batteries

open Std

def isTriangleexists (a b c : Nat) : Bool :=
  if a != 0 && b != 0 && c != 0 && (a + b + c == 180) then
    if Nat.ble c (a + b) || Nat.ble a (b + c) || Nat.ble b (a + c) then true else false
  else
    false

#guard isTriangleexists 50 60 70 == true
#guard isTriangleexists 90 45 45 == true
#guard isTriangleexists 150 30 70 == false
