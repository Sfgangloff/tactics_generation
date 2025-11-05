import Batteries

open Std

def checkLast (arr : List Int) (n p : Nat) : String :=
  let sum := arr.foldl (fun acc x => acc + x) 0
  if p == 1 then
    if sum % 2 == 0 then
      "ODD"
    else
      "EVEN"
  else
    "EVEN"

#guard checkLast [5, 7, 10] 3 1 == "ODD"
#guard checkLast [2, 3] 2 3 == "EVEN"
#guard checkLast [1, 2, 3] 3 1 == "ODD"
