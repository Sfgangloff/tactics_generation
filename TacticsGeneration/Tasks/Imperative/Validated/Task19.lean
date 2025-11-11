import Batteries



/-!
  Auto-generated from task 19.
  Module: Task19
-/

open Std

namespace Task19

def test_duplicate (arraynums : Array Nat) : Bool := Id.run do
  let mut seen : Std.HashSet Nat := Std.HashSet.empty
  for x in arraynums do
    if seen.contains x then
      return true
    seen := seen.insert x
  return false

end Task19


-- Tests
#guard (Task19.test_duplicate #[1,2,3,4,5] == false)
#guard (Task19.test_duplicate #[1,2,3,4,4] == true)
#guard (Task19.test_duplicate #[1,1,2,2,3,3,4,4,5] == true)
