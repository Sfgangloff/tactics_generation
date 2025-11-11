import Batteries

open Std

def sumSquare (n : Nat) : Bool := Id.run do
  for i in [1 : Nat.sqrt n + 1] do
    for j in [1 : Nat.sqrt n + 1] do
      if i*i + j*j == n then
        return true
  return false

#guard sumSquare 25 == true
#guard sumSquare 24 == false
#guard sumSquare 17 == true
