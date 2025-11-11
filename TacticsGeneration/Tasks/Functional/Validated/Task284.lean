import Batteries

open Std

def checkElement {α} [BEq α] (list : List α) (element : α) : Bool :=
  list.all (fun v => v == element)

#guard checkElement ["green", "orange", "black", "white"] "blue" == false
#guard checkElement [1, 2, 3, 4] 7 == false
#guard checkElement ["green", "green", "green", "green"] "green" == true
