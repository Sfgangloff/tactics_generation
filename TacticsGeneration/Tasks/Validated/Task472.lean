import Batteries

open Std

def removeOne (x : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | y :: ys => if x == y then ys else y :: removeOne x ys

def minOfList! (l : List Nat) : Nat :=
  match l with
  | [] => 0  
  | x :: xs => xs.foldl (fun acc y => Nat.min acc y) x

def maxOfList! (l : List Nat) : Nat :=
  match l with
  | [] => 0  
  | x :: xs => xs.foldl (fun acc y => Nat.max acc y) x

def selectionSort (l : List Nat) : List Nat := Id.run do
  let mut rest := l
  let mut res : List Nat := []
  let n := l.length
  for _ in [: n] do
    match rest with
    | [] => break
    | _ =>
      let m := minOfList! rest
      res := res ++ [m]
      rest := removeOne m rest
  return res

def checkConsecutive (l : List Nat) : Bool :=
  match l with
  | [] => false  
  | _ =>
    let s := selectionSort l
    let mn := minOfList! l
    let mx := maxOfList! l
    let t := (List.range (mx - mn + 1)).map (fun i => mn + i)
    s == t

#guard checkConsecutive [1, 2, 3, 4, 5] == true
#guard checkConsecutive [1, 2, 3, 5, 6] == false
#guard checkConsecutive [1, 2, 1] == false
