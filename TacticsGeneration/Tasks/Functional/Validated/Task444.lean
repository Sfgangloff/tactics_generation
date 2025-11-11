import Batteries

open Std

def joinWith (sep : String) (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: xs => xs.foldl (fun acc y => acc ++ sep ++ y) x

def formatTuple (xs : List Nat) : String :=
  match xs with
  | [] => "()"
  | [x] => "(" ++ toString x ++ ",)"
  | _ => "(" ++ joinWith ", " (xs.map (fun x => toString x)) ++ ")"

def trimTuple (test_list : List (List Nat)) (K : Nat) : String :=
  let res := test_list.map (fun ele =>
    let N := ele.length
    (ele.drop K).take (N - (K + K))
  )
  let tupleStrs := res.map formatTuple
  "[" ++ joinWith ", " tupleStrs ++ "]"

#guard trimTuple [[5, 3, 2, 1, 4], [3, 4, 9, 2, 1], [9, 1, 2, 3, 5], [4, 8, 2, 1, 7]] 2 = "[(2,), (9,), (2,), (2,)]"
#guard trimTuple [[5, 3, 2, 1, 4], [3, 4, 9, 2, 1], [9, 1, 2, 3, 5], [4, 8, 2, 1, 7]] 1 = "[(3, 2, 1), (4, 9, 2), (1, 2, 3), (8, 2, 1)]"
#guard trimTuple [[7, 8, 4, 9], [11, 8, 12, 4], [4, 1, 7, 8], [3, 6, 9, 7]] 1 = "[(8, 4), (8, 12), (1, 7), (6, 9)]"
