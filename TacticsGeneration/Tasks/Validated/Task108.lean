import Batteries

open Std

partial def removeOne (l : List Nat) (v : Nat) : List Nat :=
  match l with
  | [] => []
  | x :: xs => if x == v then xs else x :: removeOne xs v

def minOfList (l : List Nat) : Nat :=
  match l with
  | [] => 0 
  | x :: xs => xs.foldl (fun m y => if y < m then y else m) x

partial def selectionSort (l : List Nat) : List Nat :=
  let rec aux (l acc : List Nat) : List Nat :=
    match l with
    | [] => acc.reverse
    | _ =>
      let m := minOfList l
      let l' := removeOne l m
      aux l' (m :: acc)
  aux l []

partial def mergeTwo (a b : List Nat) : List Nat :=
  let rec go (a b acc : List Nat) : List Nat :=
    match a, b with
    | [], _ => acc.reverse ++ b
    | _, [] => acc.reverse ++ a
    | ha :: ta, hb :: tb =>
      if ha ≤ hb then go ta (hb :: tb) (ha :: acc)
      else go (ha :: ta) tb (hb :: acc)
  go a b []

def mergeSortedList (num1 num2 num3 : List Nat) : List Nat :=
  let num1 := selectionSort num1
  let num2 := selectionSort num2
  let num3 := selectionSort num3
  let merged12 := mergeTwo num1 num2
  let mergedAll := mergeTwo merged12 num3
  mergedAll

#guard mergeSortedList [25, 24, 15, 4, 5, 29, 110] [19, 20, 11, 56, 25, 233, 154] [24, 26, 54, 48] == [4, 5, 11, 15, 19, 20, 24, 24, 25, 25, 26, 29, 48, 54, 56, 110, 154, 233]
#guard mergeSortedList [1, 3, 5, 6, 8, 9] [2, 5, 7, 11] [1, 4, 7, 8, 12] == [1, 1, 2, 3, 4, 5, 5, 6, 7, 7, 8, 8, 9, 11, 12]
#guard mergeSortedList [18, 14, 10, 9, 8, 7, 9, 3, 2, 4, 1] [25, 35, 22, 85, 14, 65, 75, 25, 58] [12, 74, 9, 50, 61, 41] == [1, 2, 3, 4, 7, 8, 9, 9, 9, 10, 12, 14, 14, 18, 22, 25, 25, 35, 41, 50, 58, 61, 65, 74, 75, 85]
