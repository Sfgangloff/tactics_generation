import Batteries

open Std

def reverseWords (s : String) : String :=
  let words := (s.splitOn " ").filter (fun w => w != "")
  String.intercalate " " words.reverse

#guard reverseWords "python program" = "program python"
#guard reverseWords "java language" = "language java"
#guard reverseWords "indian man" = "man indian"
