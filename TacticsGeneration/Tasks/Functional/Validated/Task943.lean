import Batteries

open Std

partial def mergeGo (xs ys acc : List Nat) : List Nat :=
  match xs, ys with
  | [], _ => acc.reverse ++ ys
  | _, [] => acc.reverse ++ xs
  | x::xs', y::ys' =>
    if x ≤ y then mergeGo xs' (y::ys') (x :: acc)
    else mergeGo (x::xs') ys' (y :: acc)

def combine_lists (num1 num2 : List Nat) : List Nat :=
  mergeGo num1 num2 []

#guard combine_lists [1, 3, 5, 7, 9, 11] [0, 2, 4, 6, 8, 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
#guard combine_lists [1, 3, 5, 6, 8, 9] [2, 5, 7, 11] = [1, 2, 3, 5, 5, 6, 7, 8, 9, 11]
#guard combine_lists [1, 3, 7] [2, 4, 6] = [1, 2, 3, 4, 6, 7]
