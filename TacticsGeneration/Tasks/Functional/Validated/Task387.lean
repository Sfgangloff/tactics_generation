import Batteries

open Std

def even_or_odd (N : String) : String :=
  let l := N.length
  let last := (N.drop (l - 1)).take 1
  if last == "0" || last == "2" || last == "4" || last == "6" ||
     last == "8" || last == "A" || last == "C" || last == "E" then
    "Even"
  else
    "Odd"

#guard even_or_odd "AB3454D" == "Odd"
#guard even_or_odd "ABC" == "Even"
#guard even_or_odd "AAD" == "Odd"
