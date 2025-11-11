import Batteries



/-!
  Auto-generated from task 1.
  Module: Task1
-/

open Std

namespace Task1

/--
Preconditions:
- `m < cost.size`, `n < cost[0]!.size`
- All rows in `cost` have at least `n+1` elements.
- Uses dynamic R, C inferred from `cost`.
- Returns the minimal path cost from (0,0) to (m,n) moving right/down/diag.
-/
def min_cost (cost : Array (Array Nat)) (m n : Nat) : Nat := Id.run do
  let R := cost.size
  let C := if R == 0 then 0 else (cost[0]!).size
  -- build tc as R x C zero matrix
  let mut tc : Array (Array Nat) := #[]
  for _ in [:R] do
    let mut row : Array Nat := #[]
    for _ in [:C] do
      row := row.push 0
    tc := tc.push row
  -- tc[0][0] = cost[0][0]
  let mut row0 := tc[0]!
  row0 := row0.set! 0 ((cost[0]!)[0]!)
  tc := tc.set! 0 row0
  -- first column
  for i in [1:m+1] do
    let prev := (tc[i-1]!)[0]!
    let s := prev + (cost[i]!)[0]!
    let mut rowi := tc[i]!
    rowi := rowi.set! 0 s
    tc := tc.set! i rowi
  -- first row
  for j in [1:n+1] do
    let prev := (tc[0]!)[j-1]!
    let s := prev + (cost[0]!)[j]!
    let mut r0 := tc[0]!
    r0 := r0.set! j s
    tc := tc.set! 0 r0
  -- rest of the table
  for i in [1:m+1] do
    for j in [1:n+1] do
      let a := (tc[i-1]!)[j-1]!
      let b := (tc[i-1]!)[j]!
      let c := (tc[i]!)[j-1]!
      let mn1 := if a ≤ b then a else b
      let mn := if mn1 ≤ c then mn1 else c
      let s := mn + (cost[i]!)[j]!
      let mut rowi := tc[i]!
      rowi := rowi.set! j s
      tc := tc.set! i rowi
  return (tc[m]!)[n]!

end Task1


-- Tests
open Std
open Task1

#guard min_cost (#[(#[(1:Nat), 2, 3]), (#[(4:Nat), 8, 2]), (#[(1:Nat), 5, 3])]) 2 2 == (8:Nat)
#guard min_cost (#[(#[(2:Nat), 3, 4]), (#[(5:Nat), 9, 3]), (#[(2:Nat), 6, 4])]) 2 2 == (12:Nat)
#guard min_cost (#[(#[(3:Nat), 4, 5]), (#[(6:Nat), 10, 4]), (#[(3:Nat), 7, 5])]) 2 2 == (16:Nat)
