import Batteries



/-!
  Auto-generated from task 17.
  Module: Task17
-/

open Std

namespace Task17

/--
  Compute the perimeter of a square with side length `a`.
  Precondition: `a` is a nonnegative integer (Nat).
-/
def square_perimeter (a : Nat) : Nat := Id.run do
  let mut perimeter := 0
  perimeter := 4 * a
  return perimeter

end Task17


-- Tests
open Std

open Task17

#guard square_perimeter 10 = 40
#guard square_perimeter 5 = 20
#guard square_perimeter 4 = 16
