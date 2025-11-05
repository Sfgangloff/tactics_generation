import Batteries

open Std

def even_Power_Sum (n : Nat) : Nat := Id.run do
  let mut sum := 0
  for i in [1 : n+1] do
    let j := 2 * i
    sum := sum + j * j * j * j * j
  return sum

#guard even_Power_Sum 2 = 1056
#guard even_Power_Sum 3 = 8832
#guard even_Power_Sum 1 = 32
