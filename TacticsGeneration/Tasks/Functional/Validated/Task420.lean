import Batteries

open Std

def cube_Sum (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [1 : n + 1] do
    s := s + (2 * i) * (2 * i) * (2 * i)
  return s

#guard cube_Sum 2 = 72
#guard cube_Sum 3 = 288
#guard cube_Sum 4 = 800
