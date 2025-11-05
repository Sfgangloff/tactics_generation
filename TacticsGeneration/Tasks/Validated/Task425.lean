import Batteries

open Std

def count_element_in_list {α : Type} [BEq α] (list1 : List (List α)) (x : α) : Nat := Id.run do
  let mut ctr := 0
  for sub in list1 do
    if sub.contains x then
      ctr := ctr + 1
  return ctr

#guard count_element_in_list [[1, 3], [5, 7], [1, 11], [1, 15, 7]] 1 == 3
#guard count_element_in_list [["A", "B"], ["A", "C"], ["A", "D", "E"], ["B", "C", "D"]] "A" == 3
#guard count_element_in_list [["A", "B"], ["A", "C"], ["A", "D", "E"], ["B", "C", "D"]] "E" == 1
