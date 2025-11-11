import Batteries

open Std

def evenBitToggleNumber (n : Nat) : Nat := Id.run do
  let mut res := 0
  let mut count := 0
  let mut temp := n
  while temp > 0 do
    if count % 2 == 0 then
      res := res ||| (2 ^ count)
    count := count + 1
    temp := temp / 2
  return n ^^^ res

#guard evenBitToggleNumber 10 = 15
#guard evenBitToggleNumber 20 = 1
#guard evenBitToggleNumber 30 = 11
