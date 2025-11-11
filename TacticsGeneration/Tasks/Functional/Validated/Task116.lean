import Batteries
open Std

def tupleToInt (nums : List Nat) : Int :=
  let strNums := nums.map (toString)
  let concatenated := strNums.foldl (fun acc s => acc ++ s) ""
  match concatenated.toInt? with
  | some n => n
  | none   => 0

#guard tupleToInt [1, 2, 3] == 123
#guard tupleToInt [4, 5, 6] == 456
#guard tupleToInt [5, 6, 7] == 567
