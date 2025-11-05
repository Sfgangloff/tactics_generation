import Batteries
open Std

def findLastOccurrence (A : List Int) (x : Int) : Int :=
  let rec loop (l : List Int) (i : Int) (res : Int) : Int :=
    match l with
    | [] => res
    | v :: t =>
      let res' := if v = x then i else res
      loop t (i + 1) res'
  loop A 0 (-1)

#guard findLastOccurrence [2, 5, 5, 5, 6, 6, 8, 9, 9, 9] 5 = 3
#guard findLastOccurrence [2, 3, 5, 8, 6, 6, 8, 9, 9, 9] 9 = 9
#guard findLastOccurrence [2, 2, 1, 5, 6, 6, 6, 9, 9, 9] 6 = 6
