import Batteries

open Std

def listMin (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl Nat.min x

def listMax (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl Nat.max x

def removeListRange (list1 : List (List Nat)) (leftrange rigthrange : Nat) : List (List Nat) :=
  list1.filter (fun i => listMin i >= leftrange && listMax i <= rigthrange)

#guard removeListRange [[2], [0], [1, 2, 3], [0, 1, 2, 3, 6, 7], [9, 11], [13, 14, 15, 17]] 13 17 = [[13, 14, 15, 17]]
#guard removeListRange [[2], [0], [1, 2, 3], [0, 1, 2, 3, 6, 7], [9, 11], [13, 14, 15, 17]] 1 3 = [[2], [1, 2, 3]]
#guard removeListRange [[2], [0], [1, 2, 3], [0, 1, 2, 3, 6, 7], [9, 11], [13, 14, 15, 17]] 0 7 = [[2], [0], [1, 2, 3], [0, 1, 2, 3, 6, 7]]
