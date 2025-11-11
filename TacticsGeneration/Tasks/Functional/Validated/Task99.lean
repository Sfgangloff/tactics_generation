import Batteries

open Std

def decimalToBinary (n : Nat) : String := Id.run do
  if n == 0 then
    return "0"
  let mut x := n
  let mut res := ""
  while x > 0 do
    let d := x % 2
    res := toString d ++ res
    x := x / 2
  return res

#guard decimalToBinary 8 = "1000"
#guard decimalToBinary 18 = "10010"
#guard decimalToBinary 7 = "111"
