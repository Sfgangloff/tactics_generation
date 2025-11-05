import Batteries

open Std

def textMatchThree (text : String) : String := Id.run do
  let pattern := "abbb"
  let m := pattern.length
  let n := text.length
  let mut found := false
  for i in [0 : n - m + 1] do
    if (text.drop i).take m = pattern then
      found := true
  return if found then "Found a match!" else "Not matched!"

#guard textMatchThree "ac" == "Not matched!"
#guard textMatchThree "dc" == "Not matched!"
#guard textMatchThree "abbbba" == "Found a match!"
