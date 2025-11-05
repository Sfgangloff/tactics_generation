import Batteries

open Std

def findEqualTuple (input : List (List Nat)) (k : Nat) : Nat :=
  let flag := Id.run do
    let mut flag := 1
    for tuple in input do
      if tuple.length ≠ k then
        flag := 0
        break
    return flag
  flag

def getEqual (input : List (List Nat)) (k : Nat) : String :=
  if findEqualTuple input k == 1 then
    "All tuples have same length"
  else
    "All tuples do not have same length"

#guard getEqual [[11, 22, 33], [44, 55, 66]] 3 == "All tuples have same length"
#guard getEqual [[1, 2, 3], [4, 5, 6, 7]] 3 == "All tuples do not have same length"
#guard getEqual [[1, 2], [3, 4]] 2 == "All tuples have same length"
