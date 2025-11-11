import Batteries
open Std

def listGet? {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n+1 => listGet? xs n

def get_Inv_Count (arr : List Nat) (n : Nat) : Nat := Id.run do
  
  let mut inv_count := 0
  for i in [0 : n] do
    for j in [i+1 : n] do
      match listGet? arr i, listGet? arr j with
      | some ai, some aj =>
        if ai > aj then
          inv_count := inv_count + 1
        else
          ()
      | _, _ => ()
  return inv_count

#guard get_Inv_Count [1,20,6,4,5] 5 = 5
#guard get_Inv_Count [1,2,1] 3 = 1
#guard get_Inv_Count [1,2,5,6,1] 5 = 3
