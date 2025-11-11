import Batteries

open Std

def rightInsertion (a : List Nat) (x : Nat) : Nat :=
  a.foldl (fun acc y => if y ≤ x then acc + 1 else acc) 0

#guard rightInsertion [1,2,4,5] 6 == 4
#guard rightInsertion [1,2,4,5] 3 == 2
#guard rightInsertion [1,2,4,5] 7 == 4
