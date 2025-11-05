import Batteries

open Std

def joinWith (sep : String) (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: xs => xs.foldl (fun acc y => acc ++ sep ++ y) x

def remove_duplicate (string : String) : String := Id.run do
  let words := (string.splitOn " ").filter (fun w => w != "")
  let mut seen : HashSet String := {}
  let mut res : List String := []
  for w in words do
    if !seen.contains w then
      seen := seen.insert w
      res := res ++ [w]
  return joinWith " " res

#guard remove_duplicate "Python Exercises Practice Solution Exercises" = "Python Exercises Practice Solution"
#guard remove_duplicate "Python Exercises Practice Solution Python" = "Python Exercises Practice Solution"
#guard remove_duplicate "Python Exercises Practice Solution Practice" = "Python Exercises Practice Solution"
