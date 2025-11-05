import Batteries

open Std

def cube_Sum (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [: n] do
    s := s + (2*i + 1) * (2*i + 1) * (2*i + 1)
  return s

#guard cube_Sum 2 == 28
#guard cube_Sum 3 == 153
#guard cube_Sum 4 == 496
