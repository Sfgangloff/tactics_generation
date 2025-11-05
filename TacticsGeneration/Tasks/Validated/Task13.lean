import Batteries
open Std

abbrev Entry := (String × Nat × Nat)  

def better (a b : Entry) : Bool :=
  match a, b with
  | (_, ca, ia), (_, cb, ib) => if ca == cb then ia < ib else ca > cb

def removeAtIdx {α} (xs : List α) (i : Nat) : List α :=
  match xs, i with
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, i+1 => x :: removeAtIdx xs i

def findMaxIdx (xs : List Entry) : Option (Nat × Entry) :=
  match xs with
  | [] => none
  | x :: xs =>
    let rec loop (lst : List Entry) (i : Nat) (best : Entry) (bestIdx : Nat) : (Nat × Entry) :=
      match lst with
      | [] => (bestIdx, best)
      | y :: ys =>
        let best' := if better y best then y else best
        let bestIdx' := if better y best then i else bestIdx
        loop ys (i+1) best' bestIdx'
    some <| loop xs 1 x 0

def lookupCount (xs : List (String × Nat)) (w : String) : Option Nat :=
  match xs with
  | [] => none
  | (w', c) :: ys => if w' == w then some c else lookupCount ys w

def updateCount (xs : List (String × Nat)) (w : String) (c : Nat) : List (String × Nat) :=
  match xs with
  | [] => [(w, c)]
  | (w', d) :: ys =>
    if w' == w then
      (w, c) :: ys
    else
      (w', d) :: updateCount ys w c

def countCommon (words : List String) : List (String × Nat) := Id.run do
  let arr := words.toArray
  let mut countsList : List (String × Nat) := []
  let mut order : Array String := #[]
  for i in [0:arr.size] do
    let w := arr[i]!
    match lookupCount countsList w with
    | none =>
      countsList := (w, 1) :: countsList
      order := order.push w
    | some c =>
      countsList := updateCount countsList w (c + 1)
  
  let mut entries : List Entry := []
  for j in [0:order.size] do
    let w := order[j]!
    let c := (lookupCount countsList w).getD 0
    entries := (w, c, j) :: entries
  
  let k := 4
  let mut xs := entries
  let mut res : List (String × Nat) := []
  for _ in [:k] do
    match findMaxIdx xs with
    | none => break
    | some (j, best) =>
      let (w, c, _) := best
      res := res ++ [(w, c)]
      xs := removeAtIdx xs j
  return res

#guard countCommon ["red","green","black","pink","black","white","black","eyes","white","black","orange","pink","pink","red","red","white","orange","white","black","pink","green","green","pink","green","pink","white","orange","orange","red"] == [("pink", 6), ("black", 5), ("white", 5), ("red", 4)]
#guard countCommon ["one", "two", "three", "four", "five", "one", "two", "one", "three", "one"] == [("one", 4), ("two", 2), ("three", 2), ("four", 1)]
#guard countCommon ["Facebook", "Apple", "Amazon", "Netflix", "Google", "Apple", "Netflix", "Amazon"] == [("Apple", 2), ("Amazon", 2), ("Netflix", 2), ("Facebook", 1)]
