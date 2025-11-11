import Batteries

open Std

def digitCount (n : Nat) : Nat := (toString n).length

def countDigs (tup : List Nat) : Nat :=
  tup.foldl (fun acc x => acc + digitCount x) 0

private def insertByKey {α} (key : α → Nat) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    if Nat.ble (key y) (key x) then
      y :: insertByKey key x ys
    else
      x :: y :: ys

private def isortByKey {α} (key : α → Nat) (l : List α) : List α :=
  l.foldl (fun acc x => insertByKey key x acc) []

private def joinWith (sep : String) (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: rs => rs.foldl (fun acc s => acc ++ sep ++ s) x

private def reprTuple (t : List Nat) : String :=
  match t with
  | [] => "()"
  | [x] => "(" ++ toString x ++ ",)"
  | _ => "(" ++ joinWith ", " (t.map (fun n => toString n)) ++ ")"

private def reprListOfTuples (ts : List (List Nat)) : String :=
  "[" ++ joinWith ", " (ts.map reprTuple) ++ "]"

def sortList (testList : List (List Nat)) : String :=
  let sorted := isortByKey countDigs testList
  reprListOfTuples sorted

#guard sortList [( [3, 4, 6, 723] ), ( [1, 2] ), ( [12345] ), ( [134, 234, 34] )] = "[(1, 2), (12345,), (3, 4, 6, 723), (134, 234, 34)]"
#guard sortList [( [3, 4, 8] ), ( [1, 2] ), ( [1234335] ), ( [1345, 234, 334] )] = "[(1, 2), (3, 4, 8), (1234335,), (1345, 234, 334)]"
#guard sortList [( [34, 4, 61, 723] ), ( [1, 2] ), ( [145] ), ( [134, 23] )] = "[(1, 2), (145,), (134, 23), (34, 4, 61, 723)]"
