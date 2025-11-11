import Batteries



/-!
  Auto-generated from task 14.
  Module: Task14
-/

open Std

namespace Task14

-- Compute the volume of a triangular prism: (l * b * h) / 2
-- Preconditions: l, b, h are nonnegative (Nat)
 def find_Volume (l b h : Nat) : Nat := Id.run do
  let mut res := l
  res := res * b
  res := res * h
  res := res / 2
  return res

end Task14


-- Tests
#guard Task14.find_Volume 10 8 6 == 240
#guard Task14.find_Volume 3 2 2 == 6
#guard Task14.find_Volume 1 2 1 == 1
