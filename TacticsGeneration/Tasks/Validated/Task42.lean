import Batteries

open Std

def findSum (arr : List Int) (n : Nat) : Int :=
  arr.foldl (fun acc x => if (arr.foldl (fun count y => if y == x then count + 1 else count) 0) > 1 then acc + x else acc) 0

#guard findSum [1, 2, 3, 1, 1, 4, 5, 6] 8 == 3
#guard findSum [1, 2, 3, 1, 1] 5 == 3
#guard findSum [1, 1, 2] 3 == 2
#guard findSum [1, 1, 2, 3, 4, 5, 6, 3, 5] 9 == 18
