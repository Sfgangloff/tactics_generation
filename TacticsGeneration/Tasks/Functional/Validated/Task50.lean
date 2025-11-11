import Batteries

open Std

def minLengthList (inputList : List (List Nat)) : Nat × List Nat :=
  let minLength := inputList.foldl (fun acc x => min acc x.length) (List.head! inputList).length
  let minList := inputList.foldl (fun acc x => if x.length < acc.length then x else acc) (List.head! inputList)
  (minLength, minList)

#guard minLengthList [[0], [1, 3], [5, 7], [9, 11], [13, 15, 17]] == (1, [0])
#guard minLengthList [[1,2,3,4,5],[1,2,3,4],[1,2,3],[1,2],[1]] == (1,[1])
#guard minLengthList [[3,4,5],[6,7,8,9],[10,11,12],[1,2]] == (2,[1,2])
