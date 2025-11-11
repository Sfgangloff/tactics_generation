import Batteries

open Std

def sum_of_alternates (test_tuple : List Nat) : Nat × Nat := Id.run do
  let mut sum1 := 0
  let mut sum2 := 0
  let mut idx := 0
  for ele in test_tuple do
    if idx % 2 == 1 then
      sum1 := sum1 + ele
    else
      sum2 := sum2 + ele
    idx := idx + 1
  return (sum1, sum2)

#guard sum_of_alternates [5, 6, 3, 6, 10, 34] = (46, 18)
#guard sum_of_alternates [1, 2, 3, 4, 5] = (6, 9)
#guard sum_of_alternates [6, 7, 8, 9, 4, 5] = (21, 18)
