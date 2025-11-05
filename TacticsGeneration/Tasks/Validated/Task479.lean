import Batteries

open Std

def firstDigit (n : Nat) : Nat := Id.run do
  let mut x := n
  while x >= 10 do
    x := x / 10
  return x

#guard firstDigit 123 = 1
#guard firstDigit 456 = 4
#guard firstDigit 12 = 1
