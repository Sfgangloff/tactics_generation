import Batteries

open Std

def setLeftMostUnsetBit (n : Nat) : Nat := Id.run do
  if (n &&& (n + 1)) == 0 then
    return n
  let mut pos := 0
  let mut temp := n
  let mut count := 0
  while temp != 0 do
    if (temp &&& 1) == 0 then
      pos := count
    count := count + 1
    temp := temp >>> 1
  return n ||| (1 <<< pos)

#guard setLeftMostUnsetBit 10 = 14
#guard setLeftMostUnsetBit 12 = 14
#guard setLeftMostUnsetBit 15 = 15
