import Batteries

open Std

def firstOdd (nums : List Int) : Int :=
  match nums.find? (fun el => el.natAbs % 2 != 0) with
  | some el => el
  | none => -1

#guard firstOdd [1, 3, 5] = 1
#guard firstOdd [2, 4, 1, 3] = 1
#guard firstOdd [8, 9, 1] = 9
