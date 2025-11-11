import Batteries

open Std

def text_match (text : String) : String :=
  let patterns := "ab*?"
  if text.toList.any (fun c => c == 'a') then
    "Found a match!"
  else
    "Not matched!"

#guard text_match "msb" == "Not matched!"
#guard text_match "a0c" == "Found a match!"
#guard text_match "abbc" == "Found a match!"
