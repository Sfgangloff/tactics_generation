import Batteries



/-!
  Auto-generated from task 32.
  Module: Task32
-/

open Std

namespace Task32

-- Find the largest prime factor of a given number (n ≥ 0)
-- Preconditions follow Python's assumption that inputs are nonnegative.
-- For n = 0 or n = 1, this returns 0 (no prime factors).
def max_Prime_Factors (n : Nat) : Nat := Id.run do
  let mut n1 := n
  let mut maxPrime : Nat := 0
  -- remove factors of 2
  if n1 % 2 == 0 then
    for _ in [:n] do
      if n1 % 2 == 0 then
        maxPrime := 2
        n1 := n1 / 2
      else
        break
  -- check odd factors starting from 3
  let mut i := 3
  for _ in [:n] do
    if i * i > n1 then
      break
    if n1 % i == 0 then
      for _ in [:n] do
        if n1 % i == 0 then
          maxPrime := i
          n1 := n1 / i
        else
          break
    i := i + 2
  -- if remaining n1 is a prime > 2, it's the largest prime factor
  if n1 > 2 then
    maxPrime := n1
  return maxPrime

-- Tests mirroring Python asserts
#guard max_Prime_Factors 15 = 5
#guard max_Prime_Factors 6 = 3
#guard max_Prime_Factors 2 = 2

end Task32


-- Tests
-- Tests are included in the module above via #guard directives.
