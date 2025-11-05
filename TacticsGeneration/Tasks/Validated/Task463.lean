import Batteries

open Std

def maxSubarrayProduct (arr : List Int) : Int := Id.run do
  let n := arr.length
  let a := arr.toArray
  let mut maxEndingHere : Int := (1 : Int)
  let mut minEndingHere : Int := (1 : Int)
  let mut maxSoFar : Int := (0 : Int)
  let mut flag : Int := (0 : Int)
  for i in [0 : n] do
    let x := a[i]!
    if hpos : x > 0 then
      maxEndingHere := maxEndingHere * x
      minEndingHere := min (minEndingHere * x) (1 : Int)
      flag := 1
    else if heq : x = 0 then
      maxEndingHere := (1 : Int)
      minEndingHere := (1 : Int)
    else
      let temp := maxEndingHere
      maxEndingHere := max (minEndingHere * x) (1 : Int)
      minEndingHere := temp * x
    if maxSoFar < maxEndingHere then
      maxSoFar := maxEndingHere
  if flag = 0 && maxSoFar = 0 then
    return 0
  return maxSoFar

#guard maxSubarrayProduct [1, -2, -3, 0, 7, -8, -2] = (112 : Int)
#guard maxSubarrayProduct [6, -3, -10, 0, 2] = (180 : Int)
#guard maxSubarrayProduct [-2, -40, 0, -2, -3] = (80 : Int)
