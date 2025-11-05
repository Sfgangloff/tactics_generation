import Batteries
open Std

def adjac (ele : List Nat) (sub : List Nat := []) : List (List Nat) :=
  match ele with
  | [] => [sub]
  | x :: xs =>
    let candidates := [x - 1, x, x + 1]
    candidates.foldl (fun acc j => acc ++ adjac xs (sub ++ [j])) []

def get_coordinates (test_tup : List Nat) : List (List Nat) :=
  let res := adjac test_tup
  res

#guard get_coordinates [3, 4] == [[2, 3], [2, 4], [2, 5], [3, 3], [3, 4], [3, 5], [4, 3], [4, 4], [4, 5]]
#guard get_coordinates [4, 5] == [[3, 4], [3, 5], [3, 6], [4, 4], [4, 5], [4, 6], [5, 4], [5, 5], [5, 6]]
#guard get_coordinates [5, 6] == [[4, 5], [4, 6], [4, 7], [5, 5], [5, 6], [5, 7], [6, 5], [6, 6], [6, 7]]
