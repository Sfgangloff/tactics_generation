import Batteries
open Std

def smallestNum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0  
  | x :: xs => xs.foldl (fun acc x => if x < acc then x else acc) x

#guard smallestNum [10, 20, 1, 45, 99] == 1
#guard smallestNum [1, 2, 3] == 1
#guard smallestNum [45, 46, 50, 60] == 45
