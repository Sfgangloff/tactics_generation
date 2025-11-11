import Batteries

open Std

def highestPowerOf2 (n : Nat) : Nat := Id.run do
  let mut res := 0
  let mut i := n
  while i > 0 do
    if (i &&& (i - 1)) == 0 then
      res := i
      break
    i := i - 1
  return res

#guard highestPowerOf2 10 = 8
#guard highestPowerOf2 19 = 16
#guard highestPowerOf2 32 = 32
