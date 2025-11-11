import Batteries



/-!
  Auto-generated from task 3.
  Module: Task3
-/

open Std

def isNotPrime (n : Nat) : Bool := Id.run do
  if n < 2 then
    return true
  for x in [2 : Nat.sqrt n + 1] do
    if n % x == 0 then return true
  return false


-- Tests
#guard isNotPrime 2 == false
#guard isNotPrime 10 == true
#guard isNotPrime 35 == true
#guard isNotPrime 37 == false
#guard isNotPrime 1 == true
#guard isNotPrime 0 == true
