import Batteries
open Std

def getAt? {α} (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i+1 => getAt? xs i

def getLudic (n : Nat) : List Nat :=
  let ludics0 := (List.range n).map (fun i => i + 1)
  let rec inner (fuel2 : Nat) (first : Nat) (removeIdx : Nat) (lst : List Nat) : List Nat :=
    match fuel2 with
    | 0 => lst
    | fuel2 + 1 =>
      if removeIdx < lst.length then
        match getAt? lst removeIdx with
        | none => lst
        | some v =>
          let lst2 := lst.erase v
          let next := removeIdx + first - 1
          inner fuel2 first next lst2
      else
        lst
  let rec outer (fuel : Nat) (index : Nat) (lst : List Nat) : List Nat :=
    match fuel with
    | 0 => lst
    | fuel + 1 =>
      if index != lst.length then
        match getAt? lst index with
        | none => lst
        | some first =>
          let lst1 := inner (n + 1) first (index + first) lst
          outer fuel (index + 1) lst1
      else
        lst
  outer (n + 1) 1 ludics0

#guard getLudic 10 = [1, 2, 3, 5, 7]
#guard getLudic 25 = [1, 2, 3, 5, 7, 11, 13, 17, 23, 25]
#guard getLudic 45 = [1, 2, 3, 5, 7, 11, 13, 17, 23, 25, 29, 37, 41, 43]
