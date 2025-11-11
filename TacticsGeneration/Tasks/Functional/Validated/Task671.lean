import Batteries

open Std

def getPosOfRightMostSetBit (n : Nat) : Nat := Id.run do
  if n == 0 then return 0
  let mut pos := 1
  let mut m := n
  while m % 2 == 0 do
    pos := pos + 1
    m := m / 2
  return pos

def setRightMostUnsetBit (n : Nat) : Nat :=
  if n == 0 then
    1
  else if (n &&& (n + 1)) == 0 then
    n
  else
    let pos := getPosOfRightMostSetBit (n + 1)
    ((2 ^ (pos - 1)) ||| n)

#guard setRightMostUnsetBit 21 = 23
#guard setRightMostUnsetBit 11 = 15
#guard setRightMostUnsetBit 15 = 15
