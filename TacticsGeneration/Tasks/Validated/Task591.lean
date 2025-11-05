import Batteries

open Std

def splitLast {α} : List α → Option (List α × α)
| [] => none
| [x] => some ([], x)
| x :: xs =>
  match splitLast xs with
  | none => none
  | some (init, last) => some (x :: init, last)

def swap_List (newList : List Nat) : List Nat :=
  match newList with
  | [] => []
  | [x] => [x]
  | x :: xs =>
    match splitLast xs with
    | none => x :: xs
    | some (mid, last) => last :: mid ++ [x]

#guard swap_List [12, 35, 9, 56, 24] == [24, 35, 9, 56, 12]
#guard swap_List [1, 2, 3] == [3, 2, 1]
#guard swap_List [4, 5, 6] == [6, 5, 4]
