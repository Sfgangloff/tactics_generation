import Batteries
open Std

def insertDescAux (x : Int) (xs : List Int) (acc : List Int) (k : Nat) : List Int :=
  match xs with
  | [] =>
    let res := acc.reverse ++ [x]
    res.take k
  | y :: ys =>
    if x ≥ y then
      let res := acc.reverse ++ (x :: y :: ys)
      res.take k
    else
      insertDescAux x ys (y :: acc) k

def insertDesc (x : Int) (xs : List Int) (k : Nat) : List Int :=
  insertDescAux x xs [] k

def insertAscAux (x : Int) (xs : List Int) (acc : List Int) (k : Nat) : List Int :=
  match xs with
  | [] =>
    let res := acc.reverse ++ [x]
    res.take k
  | y :: ys =>
    if x ≤ y then
      let res := acc.reverse ++ (x :: y :: ys)
      res.take k
    else
      insertAscAux x ys (y :: acc) k

def insertAsc (x : Int) (xs : List Int) (k : Nat) : List Int :=
  insertAscAux x xs [] k

def maximumProduct (nums : List Int) : Int :=
  let a := nums.foldl (fun acc x => insertDesc x acc 3) []   
  let b := nums.foldl (fun acc x => insertAsc x acc 2) []    
  let prod1 := match a with
    | x1 :: x2 :: x3 :: _ => x1 * x2 * x3
    | _ => 0
  let prod2 := match a, b with
    | x1 :: _, y1 :: y2 :: _ => x1 * y1 * y2
    | _, _ => 0
  if prod1 ≥ prod2 then prod1 else prod2

#guard maximumProduct [12, 74, 9, 50, 61, 41] = (225700 : Int)
#guard maximumProduct [25, 35, 22, 85, 14, 65, 75, 25, 58] = (414375 : Int)
#guard maximumProduct [18, 14, 10, 9, 8, 7, 9, 3, 2, 4, 1] = (2520 : Int)
