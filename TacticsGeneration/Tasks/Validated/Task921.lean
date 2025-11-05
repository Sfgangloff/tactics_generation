import Batteries
open Std

def chunkTuples (test_tup : List Nat) (N : Nat) : List (List Nat) :=
  if N = 0 then
    []
  else
    let acc : List (List Nat) × (List Nat × Nat) :=
      test_tup.foldl
        (fun (acc : List (List Nat) × (List Nat × Nat)) (x : Nat) =>
          let res := acc.fst
          let cur := acc.snd.fst
          let cnt := acc.snd.snd
          let cnt' := cnt + 1
          if cnt' = N then
            (res ++ [cur ++ [x]], ([], 0))
          else
            (res, (cur ++ [x], cnt'))
        )
        ([], ([], 0))
    let res := acc.fst
    let cur := acc.snd.fst
    let cnt := acc.snd.snd
    if cnt = 0 then res else res ++ [cur]

#guard chunkTuples [10, 4, 5, 6, 7, 6, 8, 3, 4] 3 == [[10, 4, 5], [6, 7, 6], [8, 3, 4]]
#guard chunkTuples [1, 2, 3, 4, 5, 6, 7, 8, 9] 2 == [[1, 2], [3, 4], [5, 6], [7, 8], [9]]
#guard chunkTuples [11, 14, 16, 17, 19, 21, 22, 25] 4 == [[11, 14, 16, 17], [19, 21, 22, 25]]
