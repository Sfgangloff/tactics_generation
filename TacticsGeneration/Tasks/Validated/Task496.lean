import Batteries

open Std

def findMin? (xs : List Nat) : Option Nat :=
  match xs with
  | [] => none
  | x :: xs => some (xs.foldl (fun acc y => if y < acc then y else acc) x)

def heapQueueSmallest (nums : List Nat) (n : Nat) : List Nat :=
  let rec extract (arr : List Nat) (k : Nat) (acc : List Nat) : List Nat :=
    if k = 0 then acc.reverse
    else
      match findMin? arr with
      | none => acc.reverse
      | some m =>
        let arr' := arr.erase m
        extract arr' (k - 1) (m :: acc)
  extract nums n []

#guard heapQueueSmallest [25, 35, 22, 85, 14, 65, 75, 25, 58] 3 == [14, 22, 25]
#guard heapQueueSmallest [25, 35, 22, 85, 14, 65, 75, 25, 58] 2 == [14, 22]
#guard heapQueueSmallest [25, 35, 22, 85, 14, 65, 75, 22, 58] 5 == [14, 22, 22, 25, 35]
