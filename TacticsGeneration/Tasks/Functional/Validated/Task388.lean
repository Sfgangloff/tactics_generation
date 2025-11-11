import Batteries

open Std

def highest_Power_of_2 (n : Nat) : Nat := Id.run do
  let mut res := 0
  let mut i := n
  while i > 0 do
    if (i &&& (i - 1)) == 0 then
      res := i
      i := 0
    else
      i := i - 1
  return res

#guard highest_Power_of_2 10 = 8
#guard highest_Power_of_2 19 = 16
#guard highest_Power_of_2 32 = 32
