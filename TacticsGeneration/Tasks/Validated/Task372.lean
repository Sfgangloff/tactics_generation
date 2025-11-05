import Batteries

open Std

def findMinOpt (xs : List Nat) : Option Nat :=
  match xs with
  | [] => none
  | h :: t => some <| t.foldl (fun m x => Nat.min m x) h

def removeFirst (xs : List Nat) (y : Nat) : List Nat :=
  match xs with
  | [] => []
  | h :: t => if h == y then t else h :: removeFirst t y

def heapAssending (nums : List Nat) : List Nat := Id.run do
  let mut rem := nums
  let mut res : List Nat := []
  let n := nums.length
  for _ in [: n] do
    match findMinOpt rem with
    | none => break
    | some m =>
      res := res ++ [m]
      rem := removeFirst rem m
  return res

#guard heapAssending [18, 14, 10, 9, 8, 7, 9, 3, 2, 4, 1] == [1, 2, 3, 4, 7, 8, 9, 9, 10, 14, 18]
#guard heapAssending [25, 35, 22, 85, 14, 65, 75, 25, 58] == [14, 22, 25, 25, 35, 58, 65, 75, 85]
#guard heapAssending [1, 3, 5, 7, 9, 2, 4, 6, 8, 0] == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
