import Batteries

open Std

def firstFactorialDivisibleNumber (x : Nat) : Nat := Id.run do
  let mut i := 1
  let mut fact := 1
  for j in [1 : x] do
    fact := fact * j
    i := j
    if fact % x == 0 then
      return i
  return i

#guard firstFactorialDivisibleNumber 10 = 5
#guard firstFactorialDivisibleNumber 15 = 5
#guard firstFactorialDivisibleNumber 5 = 4
