import Batteries

open Std

def countNo (A N L R : Nat) : Nat := Id.run do
  let mut count := 0
  let mut res := L
  for i in [L : R+1] do
    if i % A != 0 then
      count := count + 1
    res := i
    if count == N then
      break
  return res

#guard countNo 2 3 1 10 = 5
#guard countNo 3 6 4 20 = 11
#guard countNo 5 10 4 20 = 16
