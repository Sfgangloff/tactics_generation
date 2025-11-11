import Batteries
open Std

/-!
  Auto-generated from task 4.
  Module: Task4
-/

def heapQueueLargest (nums : Array Nat) (n : Nat) : Array Nat := Id.run do
  -- Adjust k to not exceed the size of nums
  let mut k := n
  if k > nums.size then
    k := nums.size
  let mut res : Array Nat := #[]
  if k == 0 then
    return res
  let sz := nums.size
  -- used marks which indices have already been selected as maxima
  let mut used : Array Bool := Array.replicate sz false
  -- Repeat k times: each time pick the largest unused element
  for _ in [:k] do
    let mut found := false
    let mut maxVal := 0
    let mut maxIdx := 0
    for i in [:sz] do
      if used[i]! then
        continue
      if !found then
        found := true
        maxVal := nums[i]!
        maxIdx := i
      else
        let v := nums[i]!
        if v > maxVal then
          maxVal := v
          maxIdx := i
    if !found then
      break
    res := res.push maxVal
    used := used.set! maxIdx true
  return res


-- Tests
#guard heapQueueLargest #[25, 35, 22, 85, 14, 65, 75, 22, 58] 3 == #[85, 75, 65]
#guard heapQueueLargest #[25, 35, 22, 85, 14, 65, 75, 22, 58] 2 == #[85, 75]
#guard heapQueueLargest #[25, 35, 22, 85, 14, 65, 75, 22, 58] 5 == #[85, 75, 65, 58, 35]