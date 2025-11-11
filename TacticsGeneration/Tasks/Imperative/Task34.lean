import Batteries
open Std

/-!
  Auto-generated from task 34.
  Module: Task34
-/

/-
Preconditions (mirroring Python intent):
- `ar` is sorted ascending and has at least `N` elements.
- It contains numbers starting from 1 with exactly one missing in the first `N+1` natural numbers.
- We handle the potential mid = 0 case explicitly to avoid negative indexing.
- Returns -1 if not found (e.g., invalid inputs), matching the Python fallback.
-/
def find_missing (ar : Array Nat) (N : Nat) : Int := Id.run do
  if N == 0 then
    return -1
  let mut l := 0
  let mut r := N - 1
  -- Simulate the while loop with a bounded for-loop and manual break
  for _ in [:N+1] do
    if l > r then
      break
    let mid := (l + r) / 2
    let midVal := Array.get! ar mid -- assumes ar has at least N elements
    if midVal != mid + 1 then
      -- To avoid negative indexing, handle mid == 0 explicitly
      if mid == 0 then
        return Int.ofNat 1
      let before := Array.get! ar (mid - 1)
      if before == mid then
        return Int.ofNat (mid + 1)
      -- move left
      r := mid - 1
    else
      -- move right
      l := mid + 1
  return -1


-- Tests
#guard find_missing #[1,2,3,5] 4 == (4 : Int)
#guard find_missing #[1,3,4,5] 4 == (2 : Int)
#guard find_missing #[1,2,3,5,6,7] 5 == (4 : Int)