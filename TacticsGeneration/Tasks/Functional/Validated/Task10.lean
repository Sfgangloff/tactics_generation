import Batteries

open Std

def removeFirst (xs : List Nat) (a : Nat) : List Nat :=
  match xs with
  | []      => []
  | y :: ys => if y = a then ys else y :: removeFirst ys a

def listMin (x : Nat) (xs : List Nat) : Nat :=
  xs.foldl (fun m z => if z < m then z else m) x

def smallNNum (xs : List Nat) (n : Nat) : List Nat :=
  let rec loop (rest : List Nat) (k : Nat) (acc : List Nat) : List Nat :=
    match k with
    | 0        => acc.reverse
    | k' + 1   =>
      match rest with
      | []      => acc.reverse
      | y :: ys =>
        let m   := listMin y ys
        let rem := removeFirst (y :: ys) m
        loop rem k' (m :: acc)
  loop xs n []

#guard smallNNum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 2 == [10, 20]
#guard smallNNum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 5 == [10, 20, 20, 40, 50]
#guard smallNNum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 3 == [10, 20, 20]
