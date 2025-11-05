import Batteries

open Std

def checkK (testTup : List Nat) (K : Nat) : Bool := Id.run do
  let mut res := false
  for ele in testTup do
    if ele == K then
      res := true
      break
  return res

#guard checkK [10, 4, 5, 6, 8] 6 == true
#guard checkK [1, 2, 3, 4, 5, 6] 7 == false
#guard checkK [7, 8, 9, 44, 11, 12] 11 == true
