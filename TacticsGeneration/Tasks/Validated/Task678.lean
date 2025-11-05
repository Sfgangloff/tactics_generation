import Batteries

open Std

def removeSpaces (str1 : String) : String :=
  String.mk (List.filter (fun c => c != ' ') str1.data)

#guard removeSpaces "a b c" = "abc"
#guard removeSpaces "1 2 3" = "123"
#guard removeSpaces " b c" = "bc"
