import Batteries



/-!
  Auto-generated from task 22.
  Module: Task22
-/

open Std

namespace Task22

-- Find the first duplicate element in an array of integers.
-- Returns -1 if no duplicate exists.
def find_first_duplicate (nums : Array Int) : Int := Id.run do
  let mut numSet : Std.HashSet Int := {}
  let mut noDuplicate : Int := -1
  for i in [:nums.size] do
    let v := nums[i]!
    if numSet.contains v then
      return v
    else
      numSet := numSet.insert v
  return noDuplicate

end Task22


-- Tests
open Std

namespace Task22

#guard find_first_duplicate (#[1, 2, 3, 4, 4, 5] : Array Int) = (4 : Int)
#guard find_first_duplicate (#[1, 2, 3, 4] : Array Int) = (-1 : Int)
#guard find_first_duplicate (#[1, 1, 2, 3, 3, 2, 2] : Array Int) = (1 : Int)

end Task22
