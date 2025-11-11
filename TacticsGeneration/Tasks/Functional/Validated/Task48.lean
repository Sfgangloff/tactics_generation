import Batteries

open Std

def oddBitSetNumber (n : Nat) : Nat := Id.run do
  let L := if n == 0 then 0 else Nat.log2 n + 1
  let mut res := 0
  for count in [: L] do
    if count % 2 == 0 then
      res := res ||| (1 <<< count)
  return n ||| res

#guard oddBitSetNumber 10 = 15
#guard oddBitSetNumber 20 = 21
#guard oddBitSetNumber 30 = 31
