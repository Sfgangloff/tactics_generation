import Batteries

open Std

def _sum (arr : List Nat) : Nat :=
  arr.foldl (fun s i => s + i) 0

#guard _sum [1, 2, 3] = 6
#guard _sum [15, 12, 13, 10] = 50
#guard _sum [0, 1, 2] = 3
