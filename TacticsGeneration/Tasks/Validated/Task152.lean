import Batteries

open Std

partial def merge (a b : List Nat) : List Nat :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | ha::ta, hb::tb =>
    if ha < hb then
      ha :: merge ta b
    else
      hb :: merge a tb

partial def mergeSort (x : List Nat) : List Nat :=
  match x with
  | [] => []
  | [a] => [a]
  | _ =>
    let middle := x.length / 2
    let a := x.take middle
    let b := x.drop middle
    merge (mergeSort a) (mergeSort b)

#guard mergeSort [3, 4, 2, 6, 5, 7, 1, 9] = [1, 2, 3, 4, 5, 6, 7, 9]
#guard mergeSort [7, 25, 45, 78, 11, 33, 19] = [7, 11, 19, 25, 33, 45, 78]
#guard mergeSort [3, 1, 4, 9, 8] = [1, 3, 4, 8, 9]
