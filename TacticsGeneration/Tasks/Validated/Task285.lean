import Batteries

open Std

def textMatchTwoThree (text : String) : String := Id.run do
  let n := text.length
  for i in [0 : n + 1] do
    let t := text.drop i
    if t.take 3 == "abb" || t.take 4 == "abbb" then
      return "Found a match!"
  return "Not matched!"

#guard textMatchTwoThree "ac" = "Not matched!"
#guard textMatchTwoThree "dc" = "Not matched!"
#guard textMatchTwoThree "abbbba" = "Found a match!"
