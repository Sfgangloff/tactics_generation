import Batteries

open Std

def checkElement (testTup : List Nat) (checkList : List Nat) : Bool := Id.run do
  let mut res := false
  for ele in checkList do
    if testTup.contains ele then
      res := true
      break
  return res

#guard checkElement [4, 5, 7, 9, 3] [6, 7, 10, 11] == true
#guard checkElement [1, 2, 3, 4] [4, 6, 7, 8, 9] == true
#guard checkElement [3, 2, 1, 4, 5] [9, 8, 7, 6] == false
