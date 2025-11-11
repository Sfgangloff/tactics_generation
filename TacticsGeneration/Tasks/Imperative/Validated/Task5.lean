import Batteries
open Std

/-!
  Auto-generated from task 5.
  Module: Task5
-/

namespace Task5

/--
  Find the number of ways to tile a 3 × n board with 2 × 1 dominoes.
  Preconditions: n is a natural number (0-based). Uses dynamic programming arrays A and B.
-/
def count_ways (n : Nat) : Nat := Id.run do
  let size := n + 1
  let mut A : Array Nat := Array.replicate size 0
  let mut B : Array Nat := Array.replicate size 0
  -- Base cases
  A := A.set! 0 1
  if n >= 1 then
    A := A.set! 1 0
    B := B.set! 1 1
  -- DP transitions
  for i in [2 : n + 1] do
    let ai2 := A[i - 2]!
    let bi1 := B[i - 1]!
    let ai1 := A[i - 1]!
    let bi2 := B[i - 2]!
    let newA := ai2 + 2 * bi1
    let newB := ai1 + bi2
    A := A.set! i newA
    B := B.set! i newB
  return A[n]!

end Task5


-- Tests

open Task5

#guard count_ways 2 = 3
#guard count_ways 8 = 153
#guard count_ways 12 = 2131