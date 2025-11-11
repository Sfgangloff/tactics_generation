import Batteries

open Std

def combinationsWithReplacementAux {α : Type} (l : List α) (n : Nat) : List (List α) :=
  match n with
  | 0 => [[]]
  | Nat.succ n' =>
    let rec go (l : List α) : List (List α) :=
      match l with
      | [] => []
      | x :: xs =>
        let withX := (combinationsWithReplacementAux (x :: xs) n').map (fun rest => x :: rest)
        let withoutX := go xs
        withX ++ withoutX
    go l

def combinations_colors (l : List String) (n : Nat) : List (List String) :=
  combinationsWithReplacementAux l n

#guard combinations_colors ["Red","Green","Blue"] 1 == [["Red"], ["Green"], ["Blue"]]
#guard combinations_colors ["Red","Green","Blue"] 2 == [["Red", "Red"], ["Red", "Green"], ["Red", "Blue"], ["Green", "Green"], ["Green", "Blue"], ["Blue", "Blue"]]
#guard combinations_colors ["Red","Green","Blue"] 3 == [["Red", "Red", "Red"], ["Red", "Red", "Green"], ["Red", "Red", "Blue"], ["Red", "Green", "Green"], ["Red", "Green", "Blue"], ["Red", "Blue", "Blue"], ["Green", "Green", "Green"], ["Green", "Green", "Blue"], ["Green", "Blue", "Blue"], ["Blue", "Blue", "Blue"]]
