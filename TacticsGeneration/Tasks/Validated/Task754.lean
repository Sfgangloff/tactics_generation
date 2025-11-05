import Batteries

open Std

def extractIndexList (l1 l2 l3 : List Nat) : List Nat :=
  let rec loop (a b c : List Nat) (acc : List Nat) :=
    match a, b, c with
    | m::ma, n::nb, o::oc =>
      let acc := if m == n && n == o then acc ++ [m] else acc
      loop ma nb oc acc
    | _, _, _ => acc
  loop l1 l2 l3 []

#guard extractIndexList [1, 1, 3, 4, 5, 6, 7] [0, 1, 2, 3, 4, 5, 7] [0, 1, 2, 3, 4, 5, 7] == [1, 7]
#guard extractIndexList [1, 1, 3, 4, 5, 6, 7] [0, 1, 2, 3, 4, 6, 5] [0, 1, 2, 3, 4, 6, 7] == [1, 6]
#guard extractIndexList [1, 1, 3, 4, 6, 5, 6] [0, 1, 2, 3, 4, 5, 7] [0, 1, 2, 3, 4, 5, 7] == [1, 5]
