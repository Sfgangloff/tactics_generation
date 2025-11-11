import Batteries

open Std

def totalHammingDistance (n : Nat) : Nat := Id.run do
  let mut i := 1
  let mut s := 0
  while n / i > 0 do
    s := s + n / i
    i := i * 2
  return s

#guard totalHammingDistance 4 == 7
#guard totalHammingDistance 2 == 3
#guard totalHammingDistance 5 == 8
