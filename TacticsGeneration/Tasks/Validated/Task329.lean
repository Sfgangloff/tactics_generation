import Batteries

open Std

def negCount (list : List Int) : Nat := Id.run do
  let mut neg_count := 0
  for num in list do
    if num ≤ 0 then
      neg_count := neg_count + 1
  return neg_count

#guard negCount [-1, -2, 3, -4, -5] == 4
#guard negCount [1, 2, 3] == 0
#guard negCount [1, 2, -3, -10, 20] == 2
