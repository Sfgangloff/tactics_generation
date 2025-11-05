import Batteries

open Std

def rombus_area (p q : Nat) : Nat :=
  (p * q) / 2

#guard rombus_area 10 20 = 100
#guard rombus_area 10 5 = 25
#guard rombus_area 4 2 = 4
