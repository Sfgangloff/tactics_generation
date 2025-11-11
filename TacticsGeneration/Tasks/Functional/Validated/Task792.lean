import Batteries

open Std

def countList {α : Type} (inputList : List α) : Nat :=
  inputList.length

#guard countList [[1, 3], [5, 7], [9, 11], [13, 15, 17]] = 4
#guard countList [[1,2],[2,3],[4,5]] = 3
#guard countList [[1,0],[2,0]] = 2
