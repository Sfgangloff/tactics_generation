import Batteries

open Std

def stringToList (s : String) : List String :=
  s.splitOn " "

#guard stringToList "python programming" == ["python", "programming"]
#guard stringToList "lists tuples strings" == ["lists", "tuples", "strings"]
#guard stringToList "write a program" == ["write", "a", "program"]
