import Batteries
open Std

def flattenTuple (test_list : List (List String)) : String :=
  let flat : List String := test_list.foldr (fun sub acc => sub ++ acc) []
  match flat with
  | [] => ""
  | x :: xs => xs.foldl (fun acc s => acc ++ " " ++ s) x

#guard flattenTuple [["1", "4", "6"], ["5", "8"], ["2", "9"], ["1", "10"]] = "1 4 6 5 8 2 9 1 10"
#guard flattenTuple [["2", "3", "4"], ["6", "9"], ["3", "2"], ["2", "11"]] = "2 3 4 6 9 3 2 2 11"
#guard flattenTuple [["14", "21", "9"], ["24", "19"], ["12", "29"], ["23", "17"]] = "14 21 9 24 19 12 29 23 17"
