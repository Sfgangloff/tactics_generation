import Batteries

open Std

def findMinFloat (l : List Float) : Option Float :=
  match l with
  | [] => none
  | x::xs => some (xs.foldl (fun acc y => if y < acc then y else acc) x)

def removeOneFloat (l : List Float) (x : Float) : List Float :=
  match l with
  | [] => []
  | y::ys => if y == x then ys else y :: removeOneFloat ys x

def secondSmallest (numbers : List Float) : Option Float :=
  if numbers.length < 2 then
    none
  else if numbers.length == 2 && numbers.getD 0 0.0 == numbers.getD 1 0.0 then
    none
  else
    let uniqRev := numbers.foldl (fun acc x => if acc.contains x then acc else x :: acc) []
    let uniq := uniqRev.reverse
    match findMinFloat uniq with
    | none => none
    | some m1 =>
      match findMinFloat (removeOneFloat uniq m1) with
      | none => none
      | some m2 => some m2

#guard secondSmallest [1.0, 2.0, -8.0, -2.0, 0.0, -2.0] == some (-2.0)
#guard secondSmallest [1.0, 1.0, -0.5, 0.0, 2.0, -2.0, -2.0] == some (-0.5)
#guard secondSmallest [2.0, 2.0] == none
