import Batteries



/-!
  Auto-generated from task 35.
  Module: Task35
-/

open Std

namespace Task35

-- Find the n-th rectangular number: n * (n + 1)
def find_rect_num (n : Nat) : Nat := Id.run do
  let mut res := n * (n + 1)
  return res

end Task35


-- Tests
open Std

open Task35

#guard (find_rect_num 4 = 20)
#guard (find_rect_num 5 = 30)
#guard (find_rect_num 6 = 42)
