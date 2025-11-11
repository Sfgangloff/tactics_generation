import Batteries



/-!
  Auto-generated from task 1.
  Module: Task1
-/

open Std

def set2dNat (a : Array (Array Nat)) (y x : Nat) (value : Nat) : Array (Array Nat) :=
  a.modify y (fun row => row.set! x value)

def get2dNat (a : Array (Array Nat)) (y x : Nat) (fallback : Nat) : Nat :=
  let row := a.getD y #[]
  row.getD x fallback

/--
Preconditions:
- m and n are within the bounds of the given cost matrix (0 ≤ m < rows, 0 ≤ n < cols).
- Moves allowed: right, down, and diagonal down-right.
-/
def minCost (cost : List (List Nat)) (m n : Nat) : Nat := Id.run do
  let costA : Array (Array Nat) := (cost.map (fun r => r.toArray)).toArray
  let mut dp : Array (Array Nat) := Array.replicate (m+1) (Array.replicate (n+1) 0)
  -- base cell
  dp := set2dNat dp 0 0 (get2dNat costA 0 0 0)
  -- first column
  for i in [1 : m+1] do
    let prev := get2dNat dp (i-1) 0 0
    let c := get2dNat costA i 0 0
    dp := set2dNat dp i 0 (prev + c)
  -- first row
  for j in [1 : n+1] do
    let prev := get2dNat dp 0 (j-1) 0
    let c := get2dNat costA 0 j 0
    dp := set2dNat dp 0 j (prev + c)
  -- rest of the table
  for i in [1 : m+1] do
    for j in [1 : n+1] do
      let diag := get2dNat dp (i-1) (j-1) 0
      let up := get2dNat dp (i-1) j 0
      let left := get2dNat dp i (j-1) 0
      let best := Nat.min diag (Nat.min up left)
      let c := get2dNat costA i j 0
      dp := set2dNat dp i j (best + c)
  return get2dNat dp m n 0


-- Tests
#guard minCost [[1, 2, 3], [4, 8, 2], [1, 5, 3]] 2 2 = 8
#guard minCost [[2, 3, 4], [5, 9, 3], [2, 6, 4]] 2 2 = 12
#guard minCost [[3, 4, 5], [6, 10, 4], [3, 7, 5]] 2 2 = 16
