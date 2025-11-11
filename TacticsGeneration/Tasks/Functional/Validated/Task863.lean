import Batteries

open Std

partial def listMin (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl (fun m a => if a < m then a else m) x

partial def removeOne (l : List Nat) (x : Nat) : List Nat :=
  match l with
  | [] => []
  | y :: ys => if y == x then ys else y :: removeOne ys x

partial def selectionSortAux (xs acc : List Nat) : List Nat :=
  match xs with
  | [] => acc.reverse
  | _ =>
    let m := listMin xs
    selectionSortAux (removeOne xs m) (m :: acc)

partial def selectionSort (l : List Nat) : List Nat :=
  selectionSortAux l []

def uniqueSorted (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: xs =>
    let (_, accRev) := xs.foldl (fun (p : Nat × List Nat) a =>
      let (last, accRev) := p
      if a != last then (a, a :: accRev) else (last, accRev)
    ) (x, [x])
    accRev.reverse

def longestConsecutiveFromUnique (v : List Nat) : Nat :=
  let (_, count, ans) := v.foldl (fun (state : Option Nat × Nat × Nat) a =>
    let (prev?, count, ans) := state
    let count' :=
      match prev? with
      | some p => if a == p + 1 then count + 1 else 1
      | none => 1
    let ans' := if ans < count' then count' else ans
    (some a, count', ans')
  ) (none, 0, 0)
  ans

def findLongestConseqSubseq (arr : List Nat) (n : Nat) : Nat :=
  let arrN := arr.take n
  let sorted := selectionSort arrN
  let v := uniqueSorted sorted
  longestConsecutiveFromUnique v

#guard findLongestConseqSubseq [1, 2, 2, 3] 4 == 3
#guard findLongestConseqSubseq [1, 9, 3, 10, 4, 20, 2] 7 == 4
#guard findLongestConseqSubseq [36, 41, 56, 35, 44, 33, 34, 92, 43, 32, 42] 11 == 5
