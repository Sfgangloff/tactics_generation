import Batteries
open Std

def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [x]
  | y :: ys =>
    if x ≤ y then
      x :: y :: ys
    else
      y :: insertSorted x ys

def selectionSort (l : List Nat) : List Nat :=
  let rec sort (xs : List Nat) : List Nat :=
    match xs with
    | [] => []
    | h :: t => insertSorted h (sort t)
  sort l

def extractMinMax (testTup : List Nat) (K : Nat) : List Nat :=
  let temp := selectionSort testTup
  let n := temp.length
  let rec loop (i : Nat) (xs : List Nat) (acc : List Nat) : List Nat :=
    match xs with
    | [] => acc.reverse
    | y :: ys =>
      if i < K || i >= n - K then
        loop (i + 1) ys (y :: acc)
      else
        loop (i + 1) ys acc
  loop 0 temp []

#guard extractMinMax [5, 20, 3, 7, 6, 8] 2 = [3, 5, 8, 20]
#guard extractMinMax [4, 5, 6, 1, 2, 7] 3 = [1, 2, 4, 5, 6, 7]
#guard extractMinMax [2, 3, 4, 8, 9, 11, 7] 4 = [2, 3, 4, 7, 8, 9, 11]
