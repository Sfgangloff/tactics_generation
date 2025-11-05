import Batteries

open Std

def No_of_cubes (N K : Nat) : Nat := Id.run do
  let mut No := 0
  No := (N - K + 1)
  No := No ^ 3
  return No

#guard No_of_cubes 2 1 = 8
#guard No_of_cubes 5 2 = 64
#guard No_of_cubes 1 1 = 1
