import Batteries

open Std

def findMin? (xs : List Nat) : Option Nat :=
  match xs with
  | [] => none
  | x :: xs' => some <| xs'.foldl (fun acc y => if y < acc then y else acc) x

def removeOne (x : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | y :: ys => if y == x then ys else y :: removeOne x ys

def heapSort (iterable : List Nat) : List Nat := Id.run do
  let mut h := iterable
  let n := h.length
  let mut res : Array Nat := #[]
  for _ in [: n] do
    match findMin? h with
    | none => break
    | some m =>
      res := res.push m
      h := removeOne m h
  return res.toList

#guard heapSort [1, 3, 5, 7, 9, 2, 4, 6, 8, 0] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
#guard heapSort [25, 35, 22, 85, 14, 65, 75, 25, 58] = [14, 22, 25, 25, 35, 58, 65, 75, 85]
#guard heapSort [7, 1, 9, 5] = [1, 5, 7, 9]
