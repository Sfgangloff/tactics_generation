import Batteries

open Std

def countX (tup : List Nat) (x : Nat) : Nat := Id.run do
  let mut count := 0
  for ele in tup do
    if ele == x then
      count := count + 1
  return count

#guard countX [10, 8, 5, 2, 10, 15, 10, 8, 5, 8, 8, 2] 4 == 0
#guard countX [10, 8, 5, 2, 10, 15, 10, 8, 5, 8, 8, 2] 10 == 3
#guard countX [10, 8, 5, 2, 10, 15, 10, 8, 5, 8, 8, 2] 8 == 4
