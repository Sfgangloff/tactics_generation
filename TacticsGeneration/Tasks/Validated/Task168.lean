import Batteries

open Std

def frequency (a : List Nat) (x : Nat) : Nat := Id.run do
  let mut count := 0
  for i in a do
    if i == x then
      count := count + 1
  return count

#guard frequency [1,2,3] 4 = 0
#guard frequency [1,2,2,3,3,3,4] 3 = 3
#guard frequency [0,1,2,3,1,2] 1 = 2
