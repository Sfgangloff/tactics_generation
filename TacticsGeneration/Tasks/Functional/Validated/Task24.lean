import Batteries

open Std

def binaryToDecimal (binary : Nat) : Nat := Id.run do
  let mut binary1 := binary
  let mut decimal := 0
  let mut i := 0
  while binary1 != 0 do
    let dec := binary1 % 10
    decimal := decimal + dec * 2 ^ i
    binary1 := binary1 / 10
    i := i + 1
  return decimal

#guard binaryToDecimal 100 == 4
#guard binaryToDecimal 1011 == 11
#guard binaryToDecimal 1101101 == 109
