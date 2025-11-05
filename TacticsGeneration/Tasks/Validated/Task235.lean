import Batteries

open Std

def evenBitSetNumber (n : Nat) : Nat := Id.run do
  let mut count := 0
  let mut res := 0
  let mut temp := n
  while temp > 0 do
    if count % 2 == 1 then
      res := res ||| (Nat.shiftLeft 1 count)
    count := count + 1
    temp := Nat.shiftRight temp 1
  return n ||| res

#guard evenBitSetNumber 10 = 10
#guard evenBitSetNumber 20 = 30
#guard evenBitSetNumber 30 = 30
