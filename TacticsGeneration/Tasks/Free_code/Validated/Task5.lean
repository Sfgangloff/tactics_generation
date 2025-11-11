import Batteries
open Std



/-!
  Auto-generated from task 5.
  Module: Task5
-/

--!
/--
  countWays n returns the number of tilings of a 3×n board using 2×1 dominoes.
  Uses a standard DP with two sequences:
  - A[i]: number of full tilings of 3×i
  - B[i]: number of ways to tile 3×i with a specific single-cell deficiency pattern
  Recurrences:
    A[i] = A[i-2] + 2*B[i-1]
    B[i] = A[i-1] + B[i-2]
  Base:
    A[0] = 1, A[1] = 0, B[0] = 0, B[1] = 1
-/
def countWays (n : Nat) : Nat := Id.run do
  let mut A := Array.replicate (n+1) 0
  let mut B := Array.replicate (n+1) 0
  -- Base values
  A := A.set! 0 1
  if n >= 1 then
    -- A[1] stays 0; B[1] = 1
    B := B.set! 1 1
  if n <= 1 then
    return A[n]!
  -- DP
  for i in [2 : n+1] do
    A := A.set! i (A[i-2]! + 2 * B[i-1]!)
    B := B.set! i (A[i-1]! + B[i-2]!)
  return A[n]!


-- Tests
#guard countWays 2 == 3
#guard countWays 8 == 153
#guard countWays 12 == 2131