import Batteries

open Std

def endNum (string : String) : Bool :=
  let n := string.length
  if n = 0 then
    false
  else
    let last := string.drop (n - 1)
    last == "0" || last == "1" || last == "2" || last == "3" || last == "4" || last == "5" || last == "6" || last == "7" || last == "8" || last == "9"

#guard endNum "abcdef" == false
#guard endNum "abcdef7" == true
#guard endNum "abc" == false
