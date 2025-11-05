import Batteries
open Std

def sequential_search (dlist : List Nat) (item : Nat) : Bool × Nat :=
  let rec loop (xs : List Nat) (pos : Nat) : Bool × Nat :=
    match xs with
    | [] => (false, pos)
    | y :: ys =>
      if y == item then
        (true, pos)
      else
        loop ys (pos + 1)
  loop dlist 0

#guard sequential_search [11, 23, 58, 31, 56, 77, 43, 12, 65, 19] 31 == (true, 3)
#guard sequential_search [12, 32, 45, 62, 35, 47, 44, 61] 61 == (true, 7)
#guard sequential_search [9, 10, 17, 19, 22, 39, 48, 56] 48 == (true, 6)
