import Batteries

open Std

def search (arr : List Nat) (n : Nat) : Nat :=
  let xor := arr.foldl (fun acc x => acc ^^^ x) 0
  xor

#guard search [1,1,2,2,3] 5 == 3
#guard search [1,1,3,3,4,4,5,5,7,7,8] 11 == 8
#guard search [1,2,2,3,3,4,4] 7 == 1
