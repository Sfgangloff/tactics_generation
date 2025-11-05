import Batteries

open Std

def isAlphaStr (s : String) : Bool :=
  s.length > 0 && s.toList.all (fun c => c.isAlpha)

def hasDot (s : String) : Bool :=
  s.toList.any (fun c => c = '.')

def convElemRepr (ele : String) : String :=
  if isAlphaStr ele then
    "'" ++ ele ++ "'"
  else
    if hasDot ele then ele else ele ++ ".0"

def joinWith (sep : String) (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: xr => xr.foldl (fun acc s => acc ++ sep ++ s) x

def list_to_float (test_list : List (String × String)) : String :=
  let tuples := test_list.map (fun (a, b) => (convElemRepr a, convElemRepr b))
  let parts := tuples.map (fun (x, y) => "(" ++ x ++ ", " ++ y ++ ")")
  "[" ++ joinWith ", " parts ++ "]"

#guard list_to_float [("3", "4"), ("1", "26.45"), ("7.32", "8"), ("4", "8")] == "[(3.0, 4.0), (1.0, 26.45), (7.32, 8.0), (4.0, 8.0)]"
#guard list_to_float [("4", "4"), ("2", "27"), ("4.12", "9"), ("7", "11")] == "[(4.0, 4.0), (2.0, 27.0), (4.12, 9.0), (7.0, 11.0)]"
#guard list_to_float [("6", "78"), ("5", "26.45"), ("1.33", "4"), ("82", "13")] == "[(6.0, 78.0), (5.0, 26.45), (1.33, 4.0), (82.0, 13.0)]"
