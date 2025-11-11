import Batteries

open Std

def combinations {α} (xs : List α) (k : Nat) : List (List α) :=
  match xs, k with
  | _, 0 => [[]]
  | [], _ => []
  | x :: xs', Nat.succ k' =>
      (combinations xs' k' |>.map (fun ys => x :: ys)) ++ (combinations xs' (Nat.succ k'))

def subLists {α} (myList : List α) : List (List α) := Id.run do
  let mut subs : List (List α) := []
  let len := myList.length
  for i in [0 : len + 1] do
    let temp := combinations myList i
    if temp.length > 0 then
      subs := subs ++ temp
  return subs

#guard subLists [10, 20, 30, 40] == [[], [10], [20], [30], [40], [10, 20], [10, 30], [10, 40], [20, 30], [20, 40], [30, 40], [10, 20, 30], [10, 20, 40], [10, 30, 40], [20, 30, 40], [10, 20, 30, 40]]
#guard subLists ["X", "Y", "Z"] == [[], ["X"], ["Y"], ["Z"], ["X", "Y"], ["X", "Z"], ["Y", "Z"], ["X", "Y", "Z"]]
#guard subLists [1, 2, 3] == [[], [1], [2], [3], [1, 2], [1, 3], [2, 3], [1, 2, 3]]
