import Batteries

open Std

def insertSortedNat (x : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => [x]
  | y :: ys => if x ≤ y then x :: xs else y :: insertSortedNat x ys

def isortNat (xs : List Nat) : List Nat :=
  xs.foldl (fun acc x => insertSortedNat x acc) []

def setToTuple (s : HashSet Nat) : List Nat := Id.run do
  let mut acc : List Nat := []
  for x in s do
    acc := x :: acc
  return isortNat acc

#guard setToTuple (HashSet.ofList [1, 2, 3, 4, 5]) = [1, 2, 3, 4, 5]
#guard setToTuple (HashSet.ofList [6, 7, 8, 9, 10, 11]) = [6, 7, 8, 9, 10, 11]
#guard setToTuple (HashSet.ofList [12, 13, 14, 15, 16]) = [12, 13, 14, 15, 16]
