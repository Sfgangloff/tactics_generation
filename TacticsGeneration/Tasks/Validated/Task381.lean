import Batteries

open Std

def ltByCompare {β} [Ord β] (x y : β) : Bool :=
  match compare x y with
  | Ordering.lt => true
  | _ => false

def insertByKey {α β} [Ord β] (key : α → β) (a : α) : List α → List α
  | [] => [a]
  | b :: bs =>
    if ltByCompare (key a) (key b) then a :: b :: bs
    else b :: insertByKey key a bs

def isortByKey {α β} [Ord β] (key : α → β) (xs : List α) : List α :=
  xs.foldl (fun acc a => insertByKey key a acc) []

def indexOnInnerList (listData : List (String × Nat × Nat)) (indexNo : Nat) : List (String × Nat × Nat) :=
  match indexNo with
  | 0 => isortByKey (fun t => t.fst) listData
  | 1 => isortByKey (fun t => t.snd.fst) listData
  | 2 => isortByKey (fun t => t.snd.snd) listData
  | _ => listData

#guard indexOnInnerList [("Greyson Fulton", 98, 99), ("Brady Kent", 97, 96), ("Wyatt Knott", 91, 94), ("Beau Turnbull", 94, 98)] 0
  = [("Beau Turnbull", 94, 98), ("Brady Kent", 97, 96), ("Greyson Fulton", 98, 99), ("Wyatt Knott", 91, 94)]
#guard indexOnInnerList [("Greyson Fulton", 98, 99), ("Brady Kent", 97, 96), ("Wyatt Knott", 91, 94), ("Beau Turnbull", 94, 98)] 1
  = [("Wyatt Knott", 91, 94), ("Beau Turnbull", 94, 98), ("Brady Kent", 97, 96), ("Greyson Fulton", 98, 99)]
#guard indexOnInnerList [("Greyson Fulton", 98, 99), ("Brady Kent", 97, 96), ("Wyatt Knott", 91, 94), ("Beau Turnbull", 94, 98)] 2
  = [("Wyatt Knott", 91, 94), ("Brady Kent", 97, 96), ("Beau Turnbull", 94, 98), ("Greyson Fulton", 98, 99)]
