import Batteries



/-!
  Auto-generated from task 33.
  Module: Task33
-/

open Std

namespace Task33

-- Convert a decimal number (Nat) to its binary representation written as a decimal number
-- Example: 10 -> 1010
def decimal_To_Binary (N : Nat) : Nat := Id.run do
  let mut B_Number := 0
  let mut cnt := 0
  let mut Nmut := N
  -- Python while loop doesn't run when N == 0; return 0 directly
  if Nmut == 0 then
    return 0
  -- Upper bound on iterations: at most N + 1 divisions by 2 to reach 0
  let maxIters := Nmut + 1
  for _ in [:maxIters] do
    if Nmut == 0 then
      break
    let rem := Nmut % 2
    let c := Nat.pow 10 cnt
    B_Number := B_Number + rem * c
    Nmut := Nmut / 2
    cnt := cnt + 1
  return B_Number

end Task33


-- Tests
open Task33

#guard decimal_To_Binary 10 == 1010
#guard decimal_To_Binary 1 == 1
#guard decimal_To_Binary 20 == 10100
