import Batteries

open Std

def countOccurance (s : String) : Nat := Id.run do
  let n := s.length
  let mut count := 0
  for i in [0 : n] do
    let sub := (s.drop i).take 3
    if sub == "std" then
      count := count + 1
  return count

#guard countOccurance "letstdlenstdporstd" = 3
#guard countOccurance "truststdsolensporsd" = 1
#guard countOccurance "makestdsostdworthit" = 2
