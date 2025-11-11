import Batteries



/-!
  Auto-generated from task 17.
  Module: Task17
-/

open Std

namespace Task17

/-- Returns the perimeter of a square given the side length. -/
def squarePerimeter (side : Nat) : Nat := 4 * side

end Task17


-- Tests
#guard Task17.squarePerimeter 10 == 40
#guard Task17.squarePerimeter 5 == 20
#guard Task17.squarePerimeter 4 == 16
