import Batteries

open Std

def evenPowerSum (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [1 : n+1] do
    let j := 2 * i
    s := s + j * j * j * j
  return s

#guard evenPowerSum 2 = 272
#guard evenPowerSum 3 = 1568
#guard evenPowerSum 4 = 5664
