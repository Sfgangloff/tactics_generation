import Batteries

open Std

def Extract (lst : List (List Nat)) : List Nat :=
  lst.map (fun item =>
    match item with
    | x :: _ => x
    | [] => 0)

#guard Extract [[1, 2], [3, 4, 5], [6, 7, 8, 9]] = [1, 3, 6]
#guard Extract [[1, 2, 3], [4, 5]] = [1, 4]
#guard Extract [[9, 8, 1], [1, 2]] = [9, 1]
