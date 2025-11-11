import Batteries

open Std

def sum (N : Nat) : Nat := Id.run do
  let mut sumOfPrimeDivisors := Array.replicate (N + 1) 0
  for i in [2 : N + 1] do
    if sumOfPrimeDivisors[i]! == 0 then
      let mut j := i
      while h : j ≤ N do
        sumOfPrimeDivisors := sumOfPrimeDivisors.set! j (sumOfPrimeDivisors[j]! + i)
        j := j + i
  return sumOfPrimeDivisors[N]!

#guard sum 60 = 10
#guard sum 39 = 16
#guard sum 40 = 7
