import Batteries

open Std

def sumRangeList (list1 : List Nat) (m n : Nat) : Nat := Id.run do
  
  let mut sum_range := 0
  for i in [m : n+1] do
    sum_range := sum_range + list1.getD i 0
  return sum_range

#guard sumRangeList [2,1,5,6,8,3,4,9,10,11,8,12] 8 10 = 29
#guard sumRangeList [2,1,5,6,8,3,4,9,10,11,8,12] 5 7 = 16
#guard sumRangeList [2,1,5,6,8,3,4,9,10,11,8,12] 7 10 = 38
