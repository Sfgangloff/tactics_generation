import Batteries

open Std

def Find_Max {α : Type} (lst : List (List α)) : List α :=
  
  match lst with
  | [] => []
  | x :: xs =>
    xs.foldl (fun best y => if y.length > best.length then y else best) x

#guard Find_Max [["A"], ["A","B"], ["A","B","C"]] = ["A","B","C"]
#guard Find_Max [[1], [1,2], [1,2,3]] = [1,2,3]
#guard Find_Max [[1,1], [1,2,3], [1,5,6,1]] = [1,5,6,1]
