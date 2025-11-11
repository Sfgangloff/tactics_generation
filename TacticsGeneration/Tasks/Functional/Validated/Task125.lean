import Batteries
open Std

def findLength (string : String) (n : Nat) : Nat := Id.run do
  let mut currentSum : Int := 0
  let mut maxSum : Int := 0
  let chars := string.data.take n
  for c in chars do
    currentSum := currentSum + (if c == '0' then (1 : Int) else (-1))
    if currentSum < 0 then
      currentSum := 0
    if currentSum > maxSum then
      maxSum := currentSum
  if maxSum == 0 then
    return 0
  else
    return Int.toNat maxSum

#guard findLength "11000010001" 11 = 6
#guard findLength "10111" 5 = 1
#guard findLength "11011101100101" 14 = 2
