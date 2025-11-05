import Batteries
open Std

def insertElement {α : Type} (list : List α) (element : α) : List α :=
  list.foldr (fun x acc => element :: x :: acc) []

#guard insertElement ["Red", "Green", "Black"] "c" = ["c", "Red", "c", "Green", "c", "Black"]
#guard insertElement ["python", "java"] "program" = ["program", "python", "program", "java"]
#guard insertElement ["happy", "sad"] "laugh" = ["laugh", "happy", "laugh", "sad"]
