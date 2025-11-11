import Batteries

open Std

def textMatchZeroOne (text : String) : String :=
  let patterns := "ab?"
  if text.data.any (fun c => c == 'a') then
    "Found a match!"
  else
    "Not matched!"

#guard textMatchZeroOne "ac" == "Found a match!"
#guard textMatchZeroOne "dc" == "Not matched!"
#guard textMatchZeroOne "abbbba" == "Found a match!"
