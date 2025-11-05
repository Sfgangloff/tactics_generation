import Batteries

open Std

def countSquares (m : Nat) (n : Nat) : Nat :=
  let (m, n) := if n < m then (n, m) else (m, n)
  (m * (m + 1) * (2 * m + 1) / 6 + (n - m) * m * (m + 1) / 2)

#guard countSquares 4 3 == 20
#guard countSquares 2 2 == 5
#guard countSquares 1 1 == 1
