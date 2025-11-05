import Batteries

open Std

def insertAsc (x : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => [x]
  | y :: ys => if x ≤ y then x :: xs else y :: insertAsc x ys

def insertionSortAsc (xs : List Nat) : List Nat :=
  xs.foldl (fun acc x => insertAsc x acc) []

def sumThreeSmallestNums (lst : List Nat) : Nat :=
  let filtered := lst.filter (fun x => x > 0)
  let sorted := insertionSortAsc filtered
  (sorted.take 3).foldl (· + ·) 0

#guard sumThreeSmallestNums [10,20,30,40,50,60,7] = 37
#guard sumThreeSmallestNums [1,2,3,4,5] = 6
#guard sumThreeSmallestNums [0,1,2,3,4,5] = 6
