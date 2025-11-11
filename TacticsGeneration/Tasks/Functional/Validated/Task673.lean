import Batteries

open Std

def convert (list : List Nat) : Nat :=
  let s := list.map (fun i => toString i)
  let resStr := s.foldl (fun acc x => acc ++ x) ""
  match resStr.toNat? with
  | some n => n
  | none => 0

#guard convert [1, 2, 3] = 123
#guard convert [4, 5, 6] = 456
#guard convert [7, 8, 9] = 789
