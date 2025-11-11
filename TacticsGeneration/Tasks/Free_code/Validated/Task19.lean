import Batteries



/-!
  Auto-generated from task 19.
  Module: Task19
-/

open Std

namespace Task19

/-- Return true iff the input contains any duplicate element. -/
def hasDuplicateList (xs : List Int) : Bool := Id.run do
  let mut seen : HashSet Int := {}
  for x in xs do
    if seen.contains x then
      return true
    seen := seen.insert x
  return false

/-- Convenience wrapper for arrays. -/
def hasDuplicateArray (xs : Array Int) : Bool :=
  hasDuplicateList xs.toList

end Task19


-- Tests
#guard Task19.hasDuplicateArray #[1,2,3,4,5] == false
#guard Task19.hasDuplicateArray #[1,2,3,4,4] == true
#guard Task19.hasDuplicateArray #[1,1,2,2,3,3,4,4,5] == true

#guard Task19.hasDuplicateList [1,2,3,4,5] == false
#guard Task19.hasDuplicateList [1,2,3,4,4] == true
