import Batteries
open Std

def getOddOccurrence (arr : List Int) (arrSize : Nat) : Int :=
  let rec findOdd (i : Nat) : Int :=
    if i >= arrSize then -1 else
      let count := (List.range arrSize).foldl (fun acc j => if arr.getD i 0 == arr.getD j 0 then acc + 1 else acc) 0
      if count % 2 != 0 then arr.getD i 0 else findOdd (i + 1)
  findOdd 0

#guard getOddOccurrence [1, 2, 3, 1, 2, 3, 1] 7 == 1
#guard getOddOccurrence [1, 2, 3, 2, 3, 1, 3] 7 == 3
#guard getOddOccurrence [2, 3, 5, 4, 5, 2, 4, 3, 5, 2, 4, 4, 2] 13 == 5
