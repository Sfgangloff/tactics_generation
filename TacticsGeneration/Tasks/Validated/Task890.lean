import Batteries

open Std

def find_Extra (arr1 arr2 : List Nat) (n : Nat) : Nat := Id.run do
  for i in [0 : n] do
    if (arr1.getD i 0) != (arr2.getD i 0) then
      return i
  return n

#guard find_Extra [1,2,3,4] [1,2,3] 3 = 3
#guard find_Extra [2,4,6,8,10] [2,4,6,8] 4 = 4
#guard find_Extra [1,3,5,7,9,11] [1,3,5,7,9] 5 = 5
