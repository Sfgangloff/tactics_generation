import Batteries

open Std

def averageEven (n : Nat) : Nat := Id.run do
  
  let mut m := n
  let mut sm := 0
  let mut count := 0
  while m >= 2 do
    count := count + 1
    sm := sm + m
    m := m - 2
  return sm / count

#guard averageEven 2 = 2
#guard averageEven 4 = 3
#guard averageEven 100 = 51
