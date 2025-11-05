import Batteries

open Std

def ltList {α} [Ord α] : List α → List α → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as', b :: bs' =>
    match compare a b with
    | Ordering.lt => true
    | Ordering.gt => false
    | Ordering.eq => ltList as' bs'

def Find_Min {α} [Ord α] (lst : List (List α)) : List α :=
  match lst with
  | [] => []
  | x :: xs => xs.foldl (fun acc y => if ltList y acc then y else acc) x

#guard Find_Min [[1],[1,2],[1,2,3]] = [1]
#guard Find_Min [[1,1],[1,1,1],[1,2,7,8]] = [1,1]
#guard Find_Min [["x"],["x","y"],["x","y","z"]] = ["x"]
