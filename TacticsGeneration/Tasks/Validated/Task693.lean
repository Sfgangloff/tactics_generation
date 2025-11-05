import Batteries

open Std

def remove_multiple_spaces (text1 : String) : String :=
  let rec go (cs : List Char) (prevSpace : Bool) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      if c == ' ' then
        if prevSpace then
          go rest true acc
        else
          go rest true (' ' :: acc)
      else
        go rest false (c :: acc)
  String.mk (go text1.data false [])

#guard remove_multiple_spaces "Google      Assistant" = "Google Assistant"
#guard remove_multiple_spaces "Quad      Core" = "Quad Core"
#guard remove_multiple_spaces "ChromeCast      Built-in" = "ChromeCast Built-in"
