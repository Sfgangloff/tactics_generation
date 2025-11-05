import Batteries

open Std

def textMatchWordz (text : String) : String :=
  let n := text.length
  let rec loop (i : Nat) : Bool :=
    if i + 1 < n then
      let c := (text.drop i).take 1
      if c == "z" then true else loop (i+1)
    else false
  if loop 0 then "Found a match!" else "Not matched!"

#guard textMatchWordz "pythonz." == "Found a match!"
#guard textMatchWordz "xyz." == "Found a match!"
#guard textMatchWordz "  lang  ." == "Not matched!"
