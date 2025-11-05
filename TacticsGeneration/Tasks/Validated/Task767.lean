import Batteries
open Std

def listNth? {α} (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs', Nat.succ i' => listNth? xs' i'

def get_Pairs_Count (arr : List Int) (n : Nat) (sum : Int) : Nat := Id.run do
  
  let mut count : Nat := 0
  for i in [0 : n] do
    for j in [i+1 : n] do
      let ai? := listNth? arr i
      let aj? := listNth? arr j
      match ai?, aj? with
      | some ai, some aj =>
        if ai + aj = sum then
          count := count + 1
        else
          ()
      | _, _ => ()
  return count

#guard get_Pairs_Count [1,1,1,1] 4 2 = 6
#guard get_Pairs_Count [1,5,7,-1,5] 5 6 = 3
#guard get_Pairs_Count [1,-2,3] 3 1 = 1
