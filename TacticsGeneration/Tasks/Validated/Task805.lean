import Batteries

open Std

def sumList (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => acc + x) 0

def maxSumList (lists : List (List Nat)) : List Nat :=
  match lists with
  | [] => []
  | x :: xs =>
    let initSum := sumList x
    let (best, _) :=
      xs.foldl (fun (acc : List Nat × Nat) (curr : List Nat) =>
        let s := sumList curr
        if s > acc.snd then (curr, s) else acc
      ) (x, initSum)
    best

#guard maxSumList [[1,2,3], [4,5,6], [10,11,12], [7,8,9]] == [10, 11, 12]
#guard maxSumList [[3,2,1], [6,5,4], [12,11,10]] == [12,11,10]
#guard maxSumList [[2,3,1]] == [2,3,1]
