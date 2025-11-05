import Batteries

open Std

def posNos (list1 : List Int) : Int :=
  match list1 with
  | [] => 0
  | num :: rest => if num ≥ 0 then num else posNos rest

#guard posNos [-1, -2, 1, 2] = 1
#guard posNos [3, 4, -5] = 3
#guard posNos [-2, -3, 1] = 1
