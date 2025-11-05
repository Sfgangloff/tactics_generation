import Batteries

open Std

def longWords (n : Nat) (str : String) : List String :=
  let txt := str.splitOn " "
  txt.foldl (fun acc x => if x.length > n then acc ++ [x] else acc) []

#guard longWords 3 "python is a programming language" == ["python", "programming", "language"]
#guard longWords 2 "writing a program" == ["writing", "program"]
#guard longWords 5 "sorting list" == ["sorting"]
