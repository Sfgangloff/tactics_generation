import Batteries

open Std

def countSetBits (n : Nat) : Nat := Id.run do
  let mut nn := n
  let mut count := 0
  while nn != 0 do
    count := count + (nn % 2)
    nn := nn / 2
  return count

#guard countSetBits 2 = 1
#guard countSetBits 4 = 1
#guard countSetBits 6 = 2
