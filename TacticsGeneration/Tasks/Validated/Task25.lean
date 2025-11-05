import Batteries
open Std

def minOfList (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => t.foldl (fun m x => if x < m then x else m) h

def removeOne (x : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => if h == x then t else h :: removeOne x t

def selectionSort (l : List Nat) : List Nat :=
  Id.run do
    let mut remaining := l
    let mut acc : List Nat := []
    let len := remaining.length
    for _ in [0:len] do
      match remaining with
      | [] => pure ()
      | _ =>
        let m := minOfList remaining
        remaining := removeOne m remaining
        acc := acc ++ [m]
    return acc

def nthD (l : List Nat) (i : Nat) (d : Nat) : Nat :=
  match l.drop i with
  | [] => d
  | h :: _ => h

def findProduct (arr : List Nat) (n : Nat) : Nat := Id.run do
  let sorted := selectionSort arr
  let mut prod := 1
  for i in [0 : n] do
    let prev := if i == 0 then nthD sorted (n - 1) 0 else nthD sorted (i - 1) 0
    let curr := nthD sorted i 0
    if prev == curr then
      pure ()
    else
      prod := prod * curr
  return prod

#guard findProduct [1,1,2,3] 4 = 6
#guard findProduct [1,2,3,1,1] 5 = 6
#guard findProduct [1,1,4,5,6] 5 = 120

#guard findProduct [1,1,4,5,6,5,7,1,1,3,4] 11 = 2520
