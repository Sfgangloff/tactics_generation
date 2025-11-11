import Batteries



/-!
  Auto-generated from task 6.
  Module: Task6
-/

open Std

namespace Task6

-- Returns true iff x is a power of two (and nonzero)
def isPowerOfTwo (x : Nat) : Bool :=
  x != 0 && ((x &&& (x - 1)) == 0)

-- Returns true iff a and b differ at exactly one bit position
def differAtOneBitPos (a b : Nat) : Bool :=
  isPowerOfTwo (a ^^^ b)

end Task6


-- Tests
#guard Task6.differAtOneBitPos 13 9 == true
#guard Task6.differAtOneBitPos 15 8 == false
#guard Task6.differAtOneBitPos 2 4 == false
