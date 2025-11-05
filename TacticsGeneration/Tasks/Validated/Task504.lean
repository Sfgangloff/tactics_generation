import Batteries

open Std

def sum_Of_Series (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [1 : n + 1] do
    s := s + i * i * i
  return s

#guard sum_Of_Series 5 = 225
#guard sum_Of_Series 2 = 9
#guard sum_Of_Series 3 = 36
