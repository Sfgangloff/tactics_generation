import Batteries

open Std

def checkValid (testTup : List Bool) : Bool :=
  let res := !(testTup.any (fun ele => !ele))
  res

#guard checkValid [true, true, true, true] == true
#guard checkValid [true, false, true, true] == false
#guard checkValid [true, true, true, true] == true
