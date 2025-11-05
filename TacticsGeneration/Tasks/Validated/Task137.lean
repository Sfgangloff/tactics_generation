import Batteries

open Std

def zeroCount (nums : List Int) : Float := Id.run do
  let n := nums.length
  let mut n1 : Nat := 0
  for x in nums do
    if x == 0 then
      n1 := n1 + 1
    else
      ()
  
  
  let num := n1 * 100
  let roundedInt := (num * 2 + n) / (2 * n)
  return (Float.ofNat roundedInt) / 100.0

#guard zeroCount [0, 1, 2, -1, -5, 6, 0, -3, -2, 3, 4, 6, 8] == 0.15
#guard zeroCount [2, 1, 2, -1, -5, 6, 4, -3, -2, 3, 4, 6, 8] == 0.0
#guard zeroCount [2, 4, -6, -9, 11, -12, 14, -5, 17] == 0.0
