import Batteries
open Std

def assocInc (xs : List (Nat × Nat)) (k : Nat) : (List (Nat × Nat)) × Bool :=
  let rec go (ys : List (Nat × Nat)) : (List (Nat × Nat)) × Bool :=
    match ys with
    | [] => ([(k, 1)], true)
    | (a, b) :: t =>
        if a = k then ((k, b + 1) :: t, false)
        else
          let (t', isNew) := go t
          ((a, b) :: t', isNew)
  go xs

def assocFind (xs : List (Nat × Nat)) (k : Nat) : Nat :=
  let rec f (ys : List (Nat × Nat)) :=
    match ys with
    | [] => 0
    | (a, b) :: t => if a = k then b else f t
  f xs

def intercalateStrings (sep : String) (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: t => t.foldl (fun acc s => acc ++ sep ++ s) x

def freqElement (test_tup : List Nat) : String :=
  let rec build (l : List Nat) (counts : List (Nat × Nat)) (order : List Nat) :
      List (Nat × Nat) × List Nat :=
    match l with
    | [] => (counts, order)
    | e :: t =>
      let (counts', isNew) := assocInc counts e
      let order' := if isNew then order ++ [e] else order
      build t counts' order'
  let (counts, order) := build test_tup [] []
  let parts := order.map (fun k => toString k ++ ": " ++ toString (assocFind counts k))
  "{" ++ intercalateStrings ", " parts ++ "}"

#guard freqElement [4, 5, 4, 5, 6, 6, 5, 5, 4] = "{4: 3, 5: 4, 6: 2}"
#guard freqElement [7, 8, 8, 9, 4, 7, 6, 5, 4] = "{7: 2, 8: 2, 9: 1, 4: 2, 6: 1, 5: 1}"
#guard freqElement [1, 4, 3, 1, 4, 5, 2, 6, 2, 7] = "{1: 2, 4: 2, 3: 1, 5: 1, 2: 2, 6: 1, 7: 1}"
