import Batteries

open Std

def fifth_Power_Sum (n : Nat) : Nat := Id.run do
  let mut sm := 0
  for i in [1 : n+1] do
    sm := sm + i*i*i*i*i
  return sm

#guard fifth_Power_Sum 2 = 33
#guard fifth_Power_Sum 4 = 1300
#guard fifth_Power_Sum 3 = 276
