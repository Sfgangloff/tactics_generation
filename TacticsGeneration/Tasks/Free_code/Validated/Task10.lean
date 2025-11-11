import Batteries



/-!
  Auto-generated from task 10.
  Module: Task10
-/

open Std

/-- Find the minimum of a non-empty list. Returns `none` for empty lists. -/
def findMin? (l : List Nat) : Option Nat :=
  match l with
  | [] => none
  | x :: xs => some <| xs.foldl (fun m y => if y < m then y else m) x

/-- Remove the first occurrence of `x` from the list (if present). -/
def removeOne (x : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | y :: ys => if y == x then ys else y :: removeOne x ys

/--
Get the n smallest items from the dataset `list1` in ascending order.
If `n` exceeds the list length, returns all elements in ascending order.
-/
def smallNNum (list1 : List Nat) (n : Nat) : List Nat := Id.run do
  let mut l := list1
  let mut k := n
  let mut res : Array Nat := #[]
  while k > 0 do
    match findMin? l with
    | none => break
    | some m =>
      res := res.push m
      l := removeOne m l
      k := k - 1
  return res.toList


-- Tests
#guard smallNNum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 2 == [10,20]
#guard smallNNum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 5 == [10,20,20,40,50]
#guard smallNNum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 3 == [10,20,20]
