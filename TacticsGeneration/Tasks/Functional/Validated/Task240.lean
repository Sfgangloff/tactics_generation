import Batteries

open Std

def replace_list {α : Type u} (list1 : List α) (list2 : List α) : List α :=
  list1.take (list1.length - 1) ++ list2

#guard replace_list [1, 3, 5, 7, 9, 10] [2, 4, 6, 8] = [1, 3, 5, 7, 9, 2, 4, 6, 8]
#guard replace_list [1,2,3,4,5] [5,6,7,8] = [1,2,3,4,5,6,7,8]
#guard replace_list ["red","blue","green"] ["yellow"] = ["red","blue","yellow"]
