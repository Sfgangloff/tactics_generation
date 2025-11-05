import Batteries
open Std

def checkEquality (str : String) : String :=
  let cs := str.data
  if cs.head? == cs.getLast? then
    "Equal"
  else
    "Not Equal"

#guard checkEquality "abcda" == "Equal"
#guard checkEquality "ab" == "Not Equal"
#guard checkEquality "mad" == "Not Equal"
