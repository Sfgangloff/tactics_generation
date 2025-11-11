import Batteries

open Std

def removeOne (xs : List Nat) (x : Nat) : List Nat :=
  match xs with
  | [] => []
  | y :: ys => if y == x then ys else y :: removeOne ys x

def maxOfList (xs : List Nat) : Option Nat :=
  match xs with
  | [] => none
  | y :: ys => some <| ys.foldl (fun acc z => if z > acc then z else acc) y

def larg_nnum (list1 : List Nat) (n : Nat) : List Nat := Id.run do
  let mut xs := list1
  let mut res : List Nat := []
  for _ in [: n] do
    match maxOfList xs with
    | none => break
    | some m =>
      res := res ++ [m]
      xs := removeOne xs m
  return res

#guard larg_nnum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 2 == [100, 90]
#guard larg_nnum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 5 == [100, 90, 80, 70, 60]
#guard larg_nnum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 3 == [100, 90, 80]
