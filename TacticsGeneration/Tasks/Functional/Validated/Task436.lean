import Batteries

open Std

def negNos (list1 : List Int) : Int :=
  match list1 with
  | [] => 0 
  | num :: rest =>
    if num < 0 then num else negNos rest

#guard negNos [-1, 4, 5, -6] = -1
#guard negNos [-1, -2, 3, 4] = -1
#guard negNos [-7, -6, 8, 9] = -7
