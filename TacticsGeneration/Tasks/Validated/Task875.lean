import Batteries

open Std

def minDifference (test_list : List (Nat × Nat)) : Nat :=
  let temp := test_list.map (fun (a, b) => if b ≥ a then b - a else a - b)
  match temp with
  | [] => 0
  | t :: ts => ts.foldl (fun acc x => if x < acc then x else acc) t

#guard minDifference [(3, 5), (1, 7), (10, 3), (1, 2)] = 1
#guard minDifference [(4, 6), (12, 8), (11, 4), (2, 13)] = 2
#guard minDifference [(5, 17), (3, 9), (12, 5), (3, 24)] = 6
