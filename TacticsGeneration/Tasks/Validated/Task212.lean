import Batteries

open Std

def fourth_Power_Sum (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [1 : n+1] do
    s := s + i*i*i*i
  return s

#guard fourth_Power_Sum 2 = 17
#guard fourth_Power_Sum 4 = 354
#guard fourth_Power_Sum 6 = 2275
