import Batteries



/-!
  Auto-generated from task 4.
  Module: Task4
-/

open Std

namespace Task4

-- Find the maximum element of a non-empty list
def listMax? (xs : List Nat) : Option Nat :=
  match xs with
  | [] => none
  | x :: xs => some (xs.foldl Nat.max x)

-- Remove the first occurrence of a value from a list
def removeFirst (a : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | y :: ys => if y == a then ys else y :: removeFirst a ys

-- Repeatedly pick the current maximum and remove one occurrence, up to n times
-- Returns the selected elements in the order they were picked (descending)
def heapQueueLargest (nums : List Nat) (n : Nat) : List Nat := Id.run do
  let mut xs := nums
  let mut res : Array Nat := #[]
  for _ in [:n] do
    match listMax? xs with
    | none => break
    | some m =>
      res := res.push m
      xs := removeFirst m xs
  return res.toList

end Task4


-- Tests
#guard Task4.heapQueueLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 3 == [85, 75, 65]
#guard Task4.heapQueueLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 2 == [85, 75]
#guard Task4.heapQueueLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 5 == [85, 75, 65, 58, 35]
