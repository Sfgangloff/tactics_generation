import Batteries

open Std

def odd_Num_Sum (n : Nat) : Nat := Id.run do
  let mut j := 0
  let mut sm := 0
  for i in [1 : n + 1] do
    j := 2 * i - 1
    sm := sm + (j * j * j * j)
  return sm

#guard odd_Num_Sum 2 = 82
#guard odd_Num_Sum 3 = 707
#guard odd_Num_Sum 4 = 3108
