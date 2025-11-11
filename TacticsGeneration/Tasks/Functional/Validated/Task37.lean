import Batteries

open Std

inductive Mixed where
  | int (n : Nat)
  | str (s : String)
  deriving Repr, DecidableEq

private def strLe (a b : String) : Bool :=
  match compare a b with
  | Ordering.lt => true
  | Ordering.eq => true
  | Ordering.gt => false

private def removeOne [BEq α] (x : α) : List α → List α
  | [] => []
  | y :: ys => if x == y then ys else y :: removeOne x ys

private def findMin? (le : α → α → Bool) (xs : List α) : Option α :=
  match xs with
  | [] => none
  | x :: xs' => some <| xs'.foldl (fun m y => if le y m then y else m) x

private def selectionSortBy [BEq α] (le : α → α → Bool) (xs : List α) : List α := Id.run do
  let mut ys := xs
  let mut acc : List α := []
  let maxIters := xs.length
  for _ in [: maxIters] do
    match findMin? le ys with
    | none => break
    | some m =>
      acc := m :: acc
      ys := removeOne m ys
  return acc.reverse

def sortMixedList (mixedList : List Mixed) : List Mixed :=
  let intPart : List Nat := mixedList.filterMap (fun
    | Mixed.int n => some n
    | _ => none)
  let strPart : List String := mixedList.filterMap (fun
    | Mixed.str s => some s
    | _ => none)
  let intSorted := selectionSortBy Nat.ble intPart
  let strSorted := selectionSortBy strLe strPart
  intSorted.map Mixed.int ++ strSorted.map Mixed.str

#guard sortMixedList [Mixed.int 19, Mixed.str "red", Mixed.int 12, Mixed.str "green", Mixed.str "blue", Mixed.int 10, Mixed.str "white", Mixed.str "green", Mixed.int 1]
  = [Task37.Mixed.int 1, Task37.Mixed.int 10, Task37.Mixed.int 12, Task37.Mixed.int 19,
     Task37.Mixed.str "blue", Task37.Mixed.str "green", Task37.Mixed.str "green", Task37.Mixed.str "red", Task37.Mixed.str "white"]
#guard sortMixedList [Mixed.int 19, Mixed.str "red", Mixed.int 12, Mixed.str "green", Mixed.str "blue", Mixed.int 10, Mixed.str "white", Mixed.str "green", Mixed.int 1]
  = [Task37.Mixed.int 1, Task37.Mixed.int 10, Task37.Mixed.int 12, Task37.Mixed.int 19,
     Task37.Mixed.str "blue", Task37.Mixed.str "green", Task37.Mixed.str "green", Task37.Mixed.str "red", Task37.Mixed.str "white"]
#guard sortMixedList [Mixed.int 19, Mixed.str "red", Mixed.int 12, Mixed.str "green", Mixed.str "blue", Mixed.int 10, Mixed.str "white", Mixed.str "green", Mixed.int 1]
  = [Task37.Mixed.int 1, Task37.Mixed.int 10, Task37.Mixed.int 12, Task37.Mixed.int 19,
     Task37.Mixed.str "blue", Task37.Mixed.str "green", Task37.Mixed.str "green", Task37.Mixed.str "red", Task37.Mixed.str "white"]
