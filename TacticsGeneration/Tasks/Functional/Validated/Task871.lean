import Batteries

open Std

def areRotations (string1 string2 : String) : Bool := Id.run do
  let size1 := string1.length
  let size2 := string2.length
  if size1 != size2 then
    return false
  let temp := string1 ++ string1
  for i in [0 : size1 + 1] do
    if string2 == (temp.drop i).take size1 then
      return true
  return false

#guard areRotations "abc" "cba" == false
#guard areRotations "abcd" "cdba" == false
#guard areRotations "abacd" "cdaba" == true
