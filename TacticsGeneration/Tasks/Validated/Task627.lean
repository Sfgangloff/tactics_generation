import Batteries

open Std

def findFirstMissing (array : List Nat) (start end_ : Nat) : Nat := Id.run do
  
  let mut s := start
  let mut e := end_
  while s ≤ e do
    if s != array.getD s 0 then
      return s
    let mid := (s + e) / 2
    if array.getD mid 0 == mid then
      s := mid + 1
    else
      e := mid
  return e + 1

#guard findFirstMissing [0,1,2,3] 0 3 = 4
#guard findFirstMissing [0,1,2,6,9] 0 4 = 3
#guard findFirstMissing [2,3,5,8,9] 0 4 = 0
