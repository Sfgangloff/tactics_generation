import Batteries

open Std

def insertSorted (x : Nat) : List Nat → List Nat
| [] => [x]
| y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def isort (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | y :: ys => insertSorted y (isort ys)

def findMinSum (a b : List Nat) (n : Nat) : Nat :=
  let sa := isort a
  let sb := isort b
  let pairs := (sa.take n).zip (sb.take n)
  pairs.foldl (init := 0) (fun s p =>
    let x := p.fst
    let y := p.snd
    s + (if x ≥ y then x - y else y - x))

#guard findMinSum [3,2,1] [2,1,3] 3 = 0
#guard findMinSum [1,2,3] [4,5,6] 3 = 9
#guard findMinSum [4,1,8,7] [2,3,6,5] 4 = 6
