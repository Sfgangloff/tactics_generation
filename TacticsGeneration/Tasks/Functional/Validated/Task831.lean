import Batteries
open Std

private def getNth? {α} (xs : List α) (i : Nat) : Option α :=
  match xs.drop i with
  | [] => none
  | a :: _ => some a

def count_Pairs (arr : List Nat) (n : Nat) : Nat := Id.run do
  let mut cnt := 0
  for i in [0 : n] do
    for j in [i+1 : n] do
      match getNth? arr i, getNth? arr j with
      | some vi, some vj =>
        if decide (vi = vj) then
          cnt := cnt + 1
        else
          ()
      | _, _ => ()
  return cnt

#guard count_Pairs [1,1,1,1] 4 = 6
#guard count_Pairs [1,5,1] 3 = 1
#guard count_Pairs [3,2,1,7,8,9] 6 = 0
