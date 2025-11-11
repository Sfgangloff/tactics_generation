import Batteries
open Std

private def listGet? {α} (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs', Nat.succ j => listGet? xs' j

def getPairsCount (arr : List Int) (n : Nat) (sum : Int) : Nat := Id.run do
  
  let mut count : Nat := 0
  for i in [0 : n] do
    for j in [i + 1 : n] do
      let ai := (listGet? arr i).getD 0
      let aj := (listGet? arr j).getD 0
      if ai + aj == sum then
        count := count + 1
  return count

#guard getPairsCount [1, 5, 7, -1, 5] 5 6 = 3
#guard getPairsCount [1, 5, 7, -1] 4 6 = 2
#guard getPairsCount [1, 1, 1, 1] 4 2 = 6
