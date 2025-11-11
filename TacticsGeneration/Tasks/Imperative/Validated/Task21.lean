import Batteries



/-!
  Auto-generated from task 21.
  Module: Task21
-/

open Std

namespace Task21

-- Find the first m multiples of n: [n, 2n, ..., m*n]
-- Assumes natural numbers (non-negative). Mirrors Python's range-based construction.
def multiples_of_num (m n : Nat) : Array Nat := Id.run do
  let mut res : Array Nat := #[]
  for i in [:m] do
    let val := n * (i + 1)
    res := res.push val
  return res

end Task21


-- Tests
open Std
open Task21

#guard multiples_of_num 4 3 == #[3, 6, 9, 12]
#guard multiples_of_num 2 5 == #[5, 10]
#guard multiples_of_num 9 2 == #[2, 4, 6, 8, 10, 12, 14, 16, 18]
