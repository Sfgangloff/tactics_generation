import Batteries

open Std

def countTuplex (tuplex : List Nat) (value : Nat) : Nat :=
  tuplex.foldl (fun acc x => if x == value then acc + 1 else acc) 0

#guard countTuplex [2, 4, 5, 6, 2, 3, 4, 4, 7] 4 = 3
#guard countTuplex [2, 4, 5, 6, 2, 3, 4, 4, 7] 2 = 2
#guard countTuplex [2, 4, 7, 7, 7, 3, 4, 4, 7] 7 = 4
