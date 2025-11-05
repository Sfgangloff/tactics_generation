import Batteries
open Std

def joinWith (sep : String) (arr : List String) : String :=
  match arr with
  | [] => ""
  | x :: xs => xs.foldl (fun acc s => acc ++ sep ++ s) x

def tupleStr (l : List Nat) : String :=
  "(" ++ joinWith ", " (l.map (fun n => toString n)) ++ ")"

def flattenPairs (xss : List (List (Nat × Nat))) : List (Nat × Nat) :=
  xss.foldr (fun row acc => row ++ acc) []

def matrixToList (test_list : List (List (Nat × Nat))) : String :=
  let temp := flattenPairs test_list
  let (xs, ys) := temp.foldr (fun (a, b) (as, bs) => (a :: as, b :: bs)) ([], [])
  "[" ++ tupleStr xs ++ ", " ++ tupleStr ys ++ "]"

#guard matrixToList [[(4,5),(7,8)], [(10,13),(18,17)], [(0,4),(10,1)]] = "[(4, 7, 10, 18, 0, 10), (5, 8, 13, 17, 4, 1)]"
#guard matrixToList [[(5,6),(8,9)], [(11,14),(19,18)], [(1,5),(11,2)]] = "[(5, 8, 11, 19, 1, 11), (6, 9, 14, 18, 5, 2)]"
#guard matrixToList [[(6,7),(9,10)], [(12,15),(20,21)], [(23,7),(15,8)]] = "[(6, 9, 12, 20, 23, 15), (7, 10, 15, 21, 7, 8)]"
