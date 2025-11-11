import Batteries

open Std

def sumDivisors (a b : Nat) : Nat := Id.run do
  let mut sum := 0
  for i in [1 : min a b] do
    if a % i == 0 && b % i == 0 then
      sum := sum + i
  return sum

#guard sumDivisors 10 15 == 6
#guard sumDivisors 100 150 == 93
#guard sumDivisors 4 6 == 3
