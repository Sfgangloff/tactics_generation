import Batteries
open Std

def maxPrimeFactors (n : Nat) : Nat := Id.run do
  let mut n := n
  let mut maxPrime := 0
  while n % 2 == 0 do
    maxPrime := 2
    n := n / 2
  let sqrt_n : Nat := Nat.sqrt n
  for i in [3: sqrt_n + 1] do
    if i % 2 == 1 then
      while n % i == 0 do
        maxPrime := i
        n := n / i
  if n > 2 then
    maxPrime := n
  return maxPrime

#guard maxPrimeFactors 15 == 5
#guard maxPrimeFactors 6 == 3
#guard maxPrimeFactors 2 == 2
