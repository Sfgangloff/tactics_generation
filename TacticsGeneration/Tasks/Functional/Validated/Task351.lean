import Batteries
open Std

private def assocFind (m : List (Int × Nat)) (x : Int) : Nat :=
  let rec go (m : List (Int × Nat)) : Nat :=
    match m with
    | [] => 0
    | (y, c) :: ys =>
      if y = x then c else go ys
  go m

private def assocInc (m : List (Int × Nat)) (x : Int) : List (Int × Nat) :=
  let rec go (m : List (Int × Nat)) : List (Int × Nat) :=
    match m with
    | [] => [(x, 1)]
    | (y, c) :: ys =>
      if y = x then (y, c + 1) :: ys else (y, c) :: go ys
  go m

def firstElement (arr : List Int) (n : Nat) (k : Nat) : Int :=
  let xs := arr.take n
  let countMap := xs.foldl (fun m x => assocInc m x) ([] : List (Int × Nat))
  let rec go (ys : List Int) : Int :=
    match ys with
    | [] => -1
    | x :: ys' =>
      let c := assocFind countMap x
      if c = k then x else go ys'
  go xs

#guard firstElement [0,1,2,3,4,5] 6 1 = 0
#guard firstElement [1,2,1,3,4] 5 2 = 1
#guard firstElement [2,3,4,3,5,7,1,2,3,5] 10 2 = 2
