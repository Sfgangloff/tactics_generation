import Batteries

open Std

def countList {α : Type} (input_list : List (List α)) : Nat :=
  let n := input_list.length
  n * n

#guard countList [[0], [1, 3], [5, 7], [9, 11], [13, 15, 17]] == 25
#guard countList [[1, 3], [5, 7], [9, 11], [13, 15, 17]] == 16
#guard countList [[[2, 4]], [[6, 8], [4, 5, 8]], [[10, 12, 14]]] == 9
