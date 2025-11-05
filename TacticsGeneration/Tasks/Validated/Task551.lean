import Batteries
open Std

def extractColumn (list1 : List (List Int)) (n : Nat) : List Int :=
  list1.map (fun row =>
    match row.drop n with
    | [] => (0 : Int)
    | x :: _ => x)

#guard extractColumn [[1, 2, 3], [2, 4, 5], [1, 1, 1]] 0 = [1, 2, 1]
#guard extractColumn [[1, 2, 3], [-2, 4, -5], [1, -1, 1]] 2 = [3, -5, 1]
#guard extractColumn [[1, 3], [5, 7], [1, 3], [13, 15, 17], [5, 7], [9, 11]] 0 = [1, 5, 1, 13, 5, 9]
