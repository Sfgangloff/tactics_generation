import Batteries

open Std

def isNotPrime (n : Nat) : Bool := Id.run do
  for x in [2 : Nat.sqrt n + 1] do
    if n % x == 0 then return true
  return false

#guard isNotPrime 2 == false
#guard isNotPrime 10 == true
#guard isNotPrime 35 == true
