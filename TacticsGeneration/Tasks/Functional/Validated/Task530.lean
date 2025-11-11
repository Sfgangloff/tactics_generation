import Batteries
open Std

def negativeCount (nums : List Int) : Float := Id.run do
  
  let n := nums.length
  let mut n1 : Nat := 0
  for x in nums do
    if x < 0 then
      n1 := n1 + 1
  let ratio := (Float.ofNat n1) / (Float.ofNat n)
  let scaled := ratio * 100.0
  let k := Float.floor (scaled + 0.5)
  return k / 100.0

#guard negativeCount [0, 1, 2, -1, -5, 6, 0, -3, -2, 3, 4, 6, 8] == 0.31
#guard negativeCount [2, 1, 2, -1, -5, 6, 4, -3, -2, 3, 4, 6, 8] == 0.31
#guard negativeCount [2, 4, -6, -9, 11, -12, 14, -5, 17] == 0.44
