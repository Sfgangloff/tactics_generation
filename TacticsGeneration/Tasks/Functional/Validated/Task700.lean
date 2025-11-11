import Batteries

open Std

def leq {α} [Ord α] (a b : α) : Bool :=
  match compare a b with
  | Ordering.lt => true
  | Ordering.eq => true
  | Ordering.gt => false

def countRangeInList {α} [Ord α] (li : List α) (min : α) (max : α) : Nat :=
  li.foldl (init := 0) (fun ctr x =>
    if leq min x && leq x max then ctr + 1 else ctr)

#guard countRangeInList [10,20,30,40,40,40,70,80,99] 40 100 = 6
#guard countRangeInList ['a','b','c','d','e','f'] 'a' 'e' = 5
#guard countRangeInList [7,8,9,15,17,19,45] 15 20 = 3
