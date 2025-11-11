import Batteries

open Std

def left_insertion (a : List Nat) (x : Nat) : Nat :=
  let rec aux (l : List Nat) (i : Nat) : Nat :=
    match l with
    | [] => i
    | y :: ys => if x ≤ y then i else aux ys (i + 1)
  aux a 0

#guard left_insertion [1, 2, 4, 5] 6 = 4
#guard left_insertion [1, 2, 4, 5] 3 = 2
#guard left_insertion [1, 2, 4, 5] 7 = 4
