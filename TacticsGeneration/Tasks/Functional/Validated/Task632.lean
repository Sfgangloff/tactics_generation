import Batteries

open Std

def moveZero (numList : List Nat) : List Nat :=
  let zeroCount := numList.foldl (fun acc i => if i == 0 then acc + 1 else acc) 0
  let a := List.replicate zeroCount 0
  let x := numList.filter (fun i => i != 0)
  x ++ a

#guard moveZero [1,0,2,0,3,4] = [1,2,3,4,0,0]
#guard moveZero [2,3,2,0,0,4,0,5,0] = [2,3,2,4,5,0,0,0,0]
#guard moveZero [0,1,0,1,1] = [1,1,1,0,0]
