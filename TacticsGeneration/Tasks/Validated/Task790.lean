import Batteries

open Std

def evenPosition (nums : List Nat) : Bool := Id.run do
  for i in [0 : nums.length] do
    let xi := nums.getD i 0
    if xi % 2 == i % 2 then
      ()
    else
      return false
  return true

#guard evenPosition [3, 2, 1] == false
#guard evenPosition [1, 2, 3] == false
#guard evenPosition [2, 1, 4] == true
