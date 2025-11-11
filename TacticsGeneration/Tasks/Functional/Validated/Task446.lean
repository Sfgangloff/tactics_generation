import Batteries

open Std

def count_Occurrence {α : Type} [BEq α] (tup : List α) (lst : List α) : Nat := Id.run do
  let mut count := 0
  for item in tup do
    if lst.contains item then
      count := count + 1
  return count

#guard count_Occurrence ["a", "a", "c", "b", "d"] ["a", "b"] = 3
#guard count_Occurrence [1, 2, 3, 1, 4, 6, 7, 1, 4] [1, 4, 7] = 6
#guard count_Occurrence [1, 2, 3, 4, 5, 6] [1, 2] = 2
