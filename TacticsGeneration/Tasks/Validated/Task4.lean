import Batteries

open Std

def heapQueueLargest (nums : List Nat) (n : Nat) : List Nat := Id.run do
  let mut heap := nums.toArray.toBinaryHeap (· < ·)
  let mut res := #[]
  for _ in [: n] do
    match heap.max with
    | none => break
    | some x => res := res.push x
    heap := heap.popMax
  return res.toList

#guard heapQueueLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 3 == [85, 75, 65]
#guard heapQueueLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 2 == [85, 75]
#guard heapQueueLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 5 == [85, 75, 65, 58, 35]
