import Batteries
open Std

def ltPair (p q : Nat × Nat) : Bool :=
  if p.fst < q.fst then true
  else if q.fst < p.fst then false
  else if p.snd < q.snd then true else false

def findMinPair (xs : List (Nat × Nat)) : Option (Nat × Nat) :=
  xs.foldl (fun acc x =>
    match acc with
    | none => some x
    | some m => if ltPair x m then some x else some m
  ) none

def removeFirstPair (xs : List (Nat × Nat)) (p : Nat × Nat) : List (Nat × Nat) :=
  match xs with
  | [] => []
  | y :: ys => if y = p then ys else y :: removeFirstPair ys p

def countsFindOpt (xs : List (Nat × Nat)) (k : Nat) : Option Nat :=
  match xs with
  | [] => none
  | (k', v) :: ys => if k = k' then some v else countsFindOpt ys k

def countsInc (xs : List (Nat × Nat)) (k : Nat) : List (Nat × Nat) :=
  match xs with
  | [] => []
  | (k', v) :: ys =>
    if k = k' then
      (k', v + 1) :: ys
    else
      (k', v) :: countsInc ys k

def func (nums : List (List Nat)) (k : Nat) : List Nat := Id.run do
  if k == 0 then
    return []
  let mut counts : List (Nat × Nat) := []
  let mut order : Array Nat := #[]
  
  for row in nums do
    for i in row do
      match countsFindOpt counts i with
      | some _ =>
        counts := countsInc counts i
      | none =>
        counts := (i, 1) :: counts
        order := order.push i
  
  let mut temp : List (Nat × Nat) := []  
  for key in order.toList do
    let v := match countsFindOpt counts key with | some c => c | none => 0
    if temp.length < k then
      temp := (v, key) :: temp
      
    else
      match findMinPair temp with
      | none => ()
      | some p =>
        if v > p.fst then
          temp := removeFirstPair temp p
          temp := (v, key) :: temp
        else
          ()
  
  let pops := temp.length
  let mut result : List Nat := []
  for _ in [: pops] do
    match findMinPair temp with
    | none => ()
    | some p =>
      result := result ++ [p.snd]
      temp := removeFirstPair temp p
  return result

#guard func [[1, 2, 6], [1, 3, 4, 5, 7, 8], [1, 3, 5, 6, 8, 9], [2, 5, 7, 11], [1, 4, 7, 8, 12]] 3 == [5, 7, 1]
#guard func [[1, 2, 6], [1, 3, 4, 5, 7, 8], [1, 3, 5, 6, 8, 9], [2, 5, 7, 11], [1, 4, 7, 8, 12]] 1 == [1]
#guard func [[1, 2, 6], [1, 3, 4, 5, 7, 8], [1, 3, 5, 6, 8, 9], [2, 5, 7, 11], [1, 4, 7, 8, 12]] 5 == [6, 5, 7, 8, 1]
