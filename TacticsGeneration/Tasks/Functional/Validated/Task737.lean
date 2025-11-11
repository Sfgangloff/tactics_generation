import Batteries

open Std

def regex : String := "^[aeiouAEIOU][A-Za-z0-9_]*"

def checkStr (string : String) : String :=
  match string.data with
  | [] => "Invalid"
  | c :: _ =>
    let isVowel :=
      c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
      c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
    if isVowel then "Valid" else "Invalid"

#guard checkStr "annie" = "Valid"
#guard checkStr "dawood" = "Invalid"
#guard checkStr "Else" = "Valid"
