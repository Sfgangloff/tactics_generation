import Batteries



/-!
  Auto-generated from task 8.
  Module: Task8
-/

open Std

def square_nums (nums : Array Nat) : Array Nat := Id.run do
  -- Build result imperatively
  let mut res : Array Nat := #[]
  for x in nums do
    res := res.push (x * x)
  return res


-- Tests
#guard square_nums #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10] = #[1, 4, 9, 16, 25, 36, 49, 64, 81, 100]
#guard square_nums #[10, 20, 30] = #[100, 400, 900]
#guard square_nums #[12, 15] = #[144, 225]
