import Batteries

open Std

def checkSubset {α : Type} [DecidableEq α] (list1 list2 : List α) : Bool :=
  list2.all (fun x => list1.contains x)

#guard checkSubset [[1, 3], [5, 7], [9, 11], [13, 15, 17]] [[1, 3], [13, 15, 17]] == true
#guard checkSubset [[1, 2], [2, 3], [3, 4], [5, 6]] [[3, 4], [5, 6]] == true
#guard checkSubset [[[1, 2], [2, 3]], [[3, 4], [5, 7]]] [[[3, 4], [5, 6]]] == false
