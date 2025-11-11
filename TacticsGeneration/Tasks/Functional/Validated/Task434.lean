import Batteries

open Std

def hasAB (s : String) : Bool :=
  let rec go (cs : List Char) : Bool :=
    match cs with
    | c1 :: c2 :: rest =>
      if c1 == 'a' && c2 == 'b' then
        true
      else
        go (c2 :: rest)
    | _ => false
  go s.data

def text_match_one (text : String) : String :=
  if hasAB text then "Found a match!" else "Not matched!"

#guard text_match_one "ac" == "Not matched!"
#guard text_match_one "dc" == "Not matched!"
#guard text_match_one "abba" == "Found a match!"
