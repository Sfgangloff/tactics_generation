import Batteries
open Std

def findMinAux (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl (fun acc y => if y < acc then y else acc) x

def deleteOne (l : List Nat) (x : Nat) : List Nat :=
  match l with
  | [] => []
  | y :: ys => if y == x then ys else y :: deleteOne ys x

def selectionSortAsc (l : List Nat) : List Nat :=
  let rec loop (fuel : Nat) (rest : List Nat) (res : List Nat) : List Nat :=
    match fuel with
    | 0 => res.reverse ++ rest
    | Nat.succ fuel' =>
      match rest with
      | [] => res.reverse
      | _ =>
        let m := findMinAux rest
        let rest' := deleteOne rest m
        loop fuel' rest' (m :: res)
  loop l.length l []

def listGet? {α} (l : List α) (i : Nat) : Option α :=
  let rec go (l' : List α) (i' : Nat) : Option α :=
    match l', i' with
    | [], _ => none
    | x :: _, 0 => some x
    | _ :: xs, Nat.succ j => go xs j
  go l i

def findDiff (arr : List Nat) (n : Nat) : Int := Id.run do
  let arrSorted := selectionSortAsc arr
  let mut count : Nat := 0
  let mut maxCount : Nat := 0
  let mut minCount : Nat := n
  for i in [0 : n - 1] do
    match listGet? arrSorted i, listGet? arrSorted (i + 1) with
    | some xi, some xj =>
      if xi == xj then
        count := count + 1
        continue
      else
        maxCount := Nat.max maxCount count
        minCount := Nat.min minCount count
        count := 0
    | _, _ => pure ()
  return Int.ofNat maxCount - Int.ofNat minCount

#guard findDiff [1,1,2,2,7,8,4,5,1,4] 10 == 2
#guard findDiff [1,7,9,2,3,3,1,3,3] 9 == 3
#guard findDiff [1,2,1,2] 4 == 0
