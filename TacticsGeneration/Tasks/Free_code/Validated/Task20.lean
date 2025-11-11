import Batteries



/-!
  Auto-generated from task 20.
  Module: Task20
-/

open Std

namespace Task20

-- A Woodall number has the form n * 2^n - 1 for some n >= 1.
-- This function checks whether the given x is a Woodall number.
def isWoodall (x : Nat) : Bool := Id.run do
  let target := x + 1
  let mut n := 1
  let mut pow2 := 2
  while n * pow2 ≤ target do
    if n * pow2 == target then
      return true
    n := n + 1
    pow2 := pow2 * 2
  return false

end Task20


-- Tests
open Task20

#guard isWoodall 383 == true
#guard isWoodall 254 == false
#guard isWoodall 200 == false

#guard isWoodall 32212254719 == true
#guard isWoodall 32212254718 == false
#guard isWoodall 159 == true
