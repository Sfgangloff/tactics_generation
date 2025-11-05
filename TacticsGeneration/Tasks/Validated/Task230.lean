import Batteries

open Std

private def joinWith (sep : String) : List String -> String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ joinWith sep xs

def replaceBlank (str1 : String) (char : String) : String :=
  joinWith char (str1.splitOn " ")

#guard replaceBlank "hello people" "@" == "hello@people"
#guard replaceBlank "python program language" "$" == "python$program$language"
#guard replaceBlank "blank space" "-" == "blank-space"
