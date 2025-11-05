import Batteries

open Std

def checkSubsetList {α : Type} [DecidableEq α] (list1 list2 : List (List α)) : Bool := Id.run do
  
  
  let _l1 : List α := match list1 with | [] => [] | x :: _ => x
  let _l2 : List α := match list2 with | [] => [] | x :: _ => x
  let mut exist := true
  for i in list2 do
    if !(i ∈ list1) then
      exist := false
  return exist

#guard checkSubsetList [[1],[2],[3],[4],[5],[6],[7],[8],[9],[10],[11],[12],[13],[14]] [[12, 18, 23, 25, 45], [7, 11, 19, 24, 28], [1, 5, 8, 18, 15, 16]] == false
#guard checkSubsetList [[2, 3, 1], [4, 5], [6, 8]] [[4, 5], [6, 8]] == true
#guard checkSubsetList [["a", "b"], ["e"], ["c", "d"]] [["g"]] == false
