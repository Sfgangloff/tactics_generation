import Batteries

open Std

def getFirstSetBitPos (n : Nat) : Nat := Id.run do
  
  if n == 0 then
    return 0
  let mut x := n
  let mut pos := 1
  while x % 2 == 0 do
    x := x / 2
    pos := pos + 1
  return pos

#guard getFirstSetBitPos 12 == 3
#guard getFirstSetBitPos 18 == 2
#guard getFirstSetBitPos 16 == 5
