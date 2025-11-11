import Batteries
open Std



/-!
  Auto-generated from task 12.
  Module: Task12
-/

namespace Task12

-- Sum of a row
def rowSum (r : List Int) : Int := r.foldl (· + ·) 0

-- Enumerate a list with starting index
def enumerateFrom {α} (xs : List α) (start : Nat) : List (Nat × α) :=
  match xs with
  | [] => []
  | x :: xs' => (start, x) :: enumerateFrom xs' (start + 1)

-- Find the index and row with minimal row-sum (first occurrence on ties)
def findMinIndexBySum (rows : List (List Int)) : Option (Nat × List Int) :=
  match enumerateFrom rows 0 with
  | [] => none
  | (i, r) :: rest =>
      let init := (i, r, rowSum r)
      let (bestI, bestR, _bestS) :=
        rest.foldl
          (fun (bi, br, bs) (j, srow) =>
            let s := rowSum srow
            if s < bs then (j, srow, s) else (bi, br, bs))
          init
      some (bestI, bestR)

-- Remove exactly one element at a given index
def removeAtIndex {α} (xs : List α) (n : Nat) : List α :=
  match xs, n with
  | [], _ => []
  | _ :: xs', 0 => xs'
  | x :: xs', Nat.succ k => x :: removeAtIndex xs' k

-- Extract the minimal row and the remaining rows
def extractMin (m : List (List Int)) : Option (List Int × List (List Int)) :=
  match findMinIndexBySum m with
  | none => none
  | some (i, row) => some (row, removeAtIndex m i)

-- Selection-style sort by row sum (ascending)
def sortMatrix (m : List (List Int)) : List (List Int) :=
  let rec loop (xs : List (List Int)) (n : Nat) (acc : List (List Int)) : List (List Int) :=
    match n with
    | 0 => acc.reverse
    | Nat.succ k =>
      match extractMin xs with
      | none => acc.reverse
      | some (row, xs') => loop xs' k (row :: acc)
  loop m m.length []

end Task12


-- Tests
open Task12

#guard sortMatrix [[1, 2, 3], [2, 4, 5], [1, 1, 1]] == [[1, 1, 1], [1, 2, 3], [2, 4, 5]]
#guard sortMatrix [[1, 2, 3], [-2, 4, -5], [1, -1, 1]] == [[-2, 4, -5], [1, -1, 1], [1, 2, 3]]
#guard sortMatrix [[5, 8, 9], [6, 4, 3], [2, 1, 4]] == [[2, 1, 4], [6, 4, 3], [5, 8, 9]]