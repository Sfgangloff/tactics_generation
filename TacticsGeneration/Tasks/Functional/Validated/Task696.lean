import Batteries

open Std

def zipList {α : Type} (list1 list2 : List (List α)) : List (List α) :=
  List.zipWith (fun a b => a ++ b) list1 list2

#guard zipList [[1, 3], [5, 7], [9, 11]] [[2, 4], [6, 8], [10, 12, 14]] == [[1, 3, 2, 4], [5, 7, 6, 8], [9, 11, 10, 12, 14]]
#guard zipList [[1, 2], [3, 4], [5, 6]] [[7, 8], [9, 10], [11, 12]] == [[1, 2, 7, 8], [3, 4, 9, 10], [5, 6, 11, 12]]
#guard zipList [["a", "b"], ["c", "d"]] [["e", "f"], ["g", "h"]] == [["a", "b", "e", "f"], ["c", "d", "g", "h"]]
