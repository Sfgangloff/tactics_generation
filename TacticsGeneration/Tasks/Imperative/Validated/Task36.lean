import Batteries



/-!
  Auto-generated from task 36.
  Module: Task36
-/

open Std

namespace Task36

-- Precondition: q > 0, N > 0 (to mirror Python's while loop semantics)
def find_Nth_Digit (p q N : Nat) : Nat := Id.run do
  let mut p := p
  let mut res := 0
  for _ in [:N] do
    p := p * 10
    let r := p / q
    res := r
    p := p % q
  return res

end Task36


-- Tests
open Std

namespace Task36

#guard find_Nth_Digit 1 2 1 == 5
#guard find_Nth_Digit 3 5 1 == 6
#guard find_Nth_Digit 5 6 5 == 3

end Task36
