import Batteries

open Std

def moveLast (num_list : List Nat) : List Nat :=
  match num_list with
  | [] => []
  | h :: t =>
    let cnt := (h :: t).foldl (fun acc x => if x == h then acc + 1 else acc) 0
    let a := List.replicate cnt h
    let x := (h :: t).filter (fun i => i != h)
    x ++ a

#guard moveLast [1,2,3,4] == [2,3,4,1]
#guard moveLast [2,3,4,1,5,0] == [3,4,1,5,0,2]
#guard moveLast [5,4,3,2,1] == [4,3,2,1,5]
