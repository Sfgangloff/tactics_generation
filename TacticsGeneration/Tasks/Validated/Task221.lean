import Batteries

open Std

def firstEven (nums : List Int) : Int :=
  match nums.find? (fun el => Int.emod el 2 == 0) with
  | some x => x
  | none => -1

#guard firstEven [1, 3, 5, 7, 4, 1, 6, 8] == 4
#guard firstEven [2, 3, 4] == 2
#guard firstEven [5, 6, 7] == 6
