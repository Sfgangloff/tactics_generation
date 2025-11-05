import Batteries
open Std

def front_and_rear (test_tup : List Nat) : Nat × Nat :=
  
  let first :=
    match test_tup with
    | [] => 0
    | x :: _ => x
  let last := test_tup.foldl (fun _ x => x) 0
  (first, last)

#guard front_and_rear [10, 4, 5, 6, 7] = (10, 7)
#guard front_and_rear [1, 2, 3, 4, 5] = (1, 5)
#guard front_and_rear [6, 7, 8, 9, 10] = (6, 10)
