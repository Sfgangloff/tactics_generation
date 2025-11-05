import Batteries

open Std

def findMin (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => t.foldl (fun acc x => if x < acc then x else acc) h

def removeOne (l : List Nat) (x : Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => if h == x then t else h :: removeOne t x

def selectionSort (l : List Nat) : List Nat :=
  let rec loop (lst : List Nat) (k : Nat) (res : List Nat) : List Nat :=
    match k with
    | 0 => res
    | k'+1 =>
      match lst with
      | [] => res
      | _ =>
        let m := findMin lst
        let lst' := removeOne lst m
        loop lst' k' (res ++ [m])
  loop l l.length []

def are_Equal (arr1 arr2 : List Nat) (n m : Nat) : Bool := Id.run do
  if n == m then
    let s1 := selectionSort arr1
    let s2 := selectionSort arr2
    for i in [0 : n - 1] do
      if (s1.getD i 0) == (s2.getD i 0) then
        pure ()
      else
        return false
    return true
  else
    return false

#guard are_Equal [1,2,3] [3,2,1] 3 3 == true
#guard are_Equal [1,1,1] [2,2,2] 3 3 == false
#guard are_Equal [8,9] [4,5,6] 2 3 == false
