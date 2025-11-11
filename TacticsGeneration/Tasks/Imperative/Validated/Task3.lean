import Batteries



/-!
  Auto-generated from task 3.
  Module: Task3
-/

open Std

namespace Task3

/--
  Identify non-prime numbers.
  Mirrors Python's logic: checks divisors i from 2 upward, stopping when i*i > n.
  For n = 0 or 1, returns false (as in the given Python function).
-/
def is_not_prime (n : Nat) : Bool := Id.run do
  let mut result := false
  let mut i := 2
  -- Use a bounded for-loop and break when i*i > n (emulating sqrt bound)
  for _ in [:n] do
    if i * i > n then
      break
    if n % i == 0 then
      result := true
    i := i + 1
  return result

end Task3


-- Tests
open Std

open Task3

#guard is_not_prime 2 == false
#guard is_not_prime 10 == true
#guard is_not_prime 35 == true
