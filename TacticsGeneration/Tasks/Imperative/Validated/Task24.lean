import Batteries



/-!
  Auto-generated from task 24.
  Module: Task24
-/

open Std

namespace Task24

-- Convert a nonnegative integer whose decimal digits are a binary number into its decimal value.
-- Preconditions: `binary` is a Nat whose digits are only 0 or 1.
def binary_to_decimal (binary : Nat) : Nat := Id.run do
  let mut b := binary
  let mut decimal := 0
  let mut i := 0
  -- Simulate a while loop using a bounded for with early break.
  for _ in [:binary + 1] do
    if b == 0 then break
    let decDigit := b % 10
    decimal := decimal + decDigit * Nat.pow 2 i
    b := b / 10
    i := i + 1
  return decimal

end Task24


-- Tests
open Std

open Task24

#guard binary_to_decimal 100 == 4
#guard binary_to_decimal 1011 == 11
#guard binary_to_decimal 1101101 == 109
