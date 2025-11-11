import Batteries
open Std

def getProduct (val : List Nat) : Nat :=
  val.foldl (fun acc ele => acc * ele) 1

def indexOrDefault (xs : List Nat) (n : Nat) (defVal : Nat) : Nat :=
  match xs, n with
  | [], _ => defVal
  | x :: _, 0 => x
  | _ :: xs', n' + 1 => indexOrDefault xs' n' defVal

def findKProduct (testList : List (List Nat)) (K : Nat) : Nat :=
  let vals := testList.map (fun sub => indexOrDefault sub K 0)
  getProduct vals

#guard findKProduct [[5, 6, 7], [1, 3, 5], [8, 9, 19]] 2 = 665
#guard findKProduct [[6, 7, 8], [2, 4, 6], [9, 10, 20]] 1 = 280
#guard findKProduct [[7, 8, 9], [3, 5, 7], [10, 11, 21]] 0 = 210
