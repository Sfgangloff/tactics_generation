import Batteries

open Std

def countSetBits (n : Nat) : Nat := Id.run do
  let n1 := n + 1
  let mut powerOf2 := 2
  let mut cnt := n1 / 2
  while powerOf2 <= n1 do
    let totalPairs := n1 / powerOf2
    cnt := cnt + (totalPairs / 2) * powerOf2
    if totalPairs % 2 == 1 then
      cnt := cnt + (n1 % powerOf2)
    else
      cnt := cnt + 0
    powerOf2 := powerOf2 * 2
  return cnt

#guard countSetBits 16 = 33
#guard countSetBits 2 = 2
#guard countSetBits 14 = 28
