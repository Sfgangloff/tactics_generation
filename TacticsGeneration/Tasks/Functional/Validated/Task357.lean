import Batteries

open Std

def findMax (test_list : List (List Nat)) : Nat := Id.run do
  let mut res : Nat := 0
  for i in test_list do
    for j in i do
      if j > res then
        res := j
  return res

#guard findMax [[2, 4], [6, 7], [5, 1], [6, 10], [8, 7]] = 10
#guard findMax [[3, 5], [7, 8], [6, 2], [7, 11], [9, 8]] = 11
#guard findMax [[4, 6], [8, 9], [7, 3], [8, 12], [10, 9]] = 12
