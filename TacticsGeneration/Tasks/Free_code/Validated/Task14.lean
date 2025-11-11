import Batteries



/-!
  Auto-generated from task 14.
  Module: Task14
-/

open Std

namespace Task14

/--
  Volume of a triangular prism with base `b`, height of the triangular base `h`,
  and length `l` is (b * h * l) / 2.
  Assumes inputs are non-negative integers and the result is integral for given tests.
-/
def findVolume (b h l : Nat) : Nat :=
  (b * h * l) / 2

end Task14


-- Tests
#guard Task14.findVolume 10 8 6 = 240
#guard Task14.findVolume 3 2 2 = 6
#guard Task14.findVolume 1 2 1 = 1
