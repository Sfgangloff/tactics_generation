import Batteries
open Std

def removeOne (xs : List Nat) (x : Nat) : List Nat :=
  match xs with
  | [] => []
  | y :: ys => if y == x then ys else y :: removeOne ys x

def findListMin (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => ys.foldl (fun m z => if z < m then z else m) y

def selectionSort (xs : List Nat) : List Nat :=
  let rec aux (k : Nat) (xs : List Nat) (res : List Nat) : List Nat :=
    match k with
    | 0 => res
    | Nat.succ k' =>
      match xs with
      | [] => res
      | _  =>
        let m := findListMin xs
        let xs' := removeOne xs m
        aux k' xs' (res ++ [m])
  aux xs.length xs []

def findMinDiff (arr : List Nat) (n : Nat) : Nat :=
  let sorted := selectionSort arr
  let sortedN := sorted.take n
  match sortedN with
  | [] => 10 ^ 20
  | [_] => 10 ^ 20
  | x :: xs =>
    let (_, res) := xs.foldl
      (fun (pAcc : Nat × Nat) (y : Nat) =>
        let p := pAcc.fst
        let acc := pAcc.snd
        let d := y - p
        let acc' := if d < acc then d else acc
        (y, acc')
      ) (x, 10 ^ 20)
    res

#guard findMinDiff [1, 5, 3, 19, 18, 25] 6 = 1
#guard findMinDiff [4, 3, 2, 6] 4 = 1
#guard findMinDiff [30, 5, 20, 9] 4 = 4
