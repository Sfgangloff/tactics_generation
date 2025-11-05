import Batteries

open Std

def sumDigits (n : Nat) : Nat := Id.run do
  let mut m := n
  let mut s := 0
  while m != 0 do
    s := s + m % 10
    m := m / 10
  return s

#guard sumDigits 345 = 12
#guard sumDigits 12 = 3
#guard sumDigits 97 = 16
