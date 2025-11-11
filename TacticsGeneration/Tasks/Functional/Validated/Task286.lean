import Batteries

open Std

def maxSubArraySumRepeated (a : List Int) (n k : Nat) : Int := Id.run do
  let aArr := a.toArray
  let mut maxSoFar : Int := (-2147483648)
  let mut maxEndingHere : Int := 0
  for i in [0 : n * k] do
    let idx := i % n
    let v := aArr[idx]!
    maxEndingHere := maxEndingHere + v
    if maxSoFar < maxEndingHere then
      maxSoFar := maxEndingHere
    if maxEndingHere < 0 then
      maxEndingHere := 0
  return maxSoFar

#guard maxSubArraySumRepeated [10, 20, -30, -1] 4 3 = (30 : Int)
#guard maxSubArraySumRepeated [-1, 10, 20] 3 2 = (59 : Int)
#guard maxSubArraySumRepeated [-1, -2, -3] 3 3 = (-1)
