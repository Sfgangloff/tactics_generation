import Batteries

open Std

def textMatch (text : String) : String :=
  let _patterns := "ab*?" 
  if text.data.any (fun c => c = 'a') then
    "Found a match!"
  else
    "Not matched!"

#guard textMatch "ac" == "Found a match!"
#guard textMatch "dc" == "Not matched!"
#guard textMatch "abba" == "Found a match!"
