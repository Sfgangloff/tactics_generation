import Batteries

open Std

def containsSubstr (s sub : String) : Bool := Id.run do
  if sub.length == 0 then
    return true
  if sub.length > s.length then
    return false
  let limit := s.length - sub.length + 1
  for i in [0 : limit] do
    if ((s.drop i).take sub.length) == sub then
      return true
  return false

def findSubstring (str1 : List String) (sub_str : String) : Bool :=
  str1.any (fun s => containsSubstr s sub_str)

#guard findSubstring ["red", "black", "white", "green", "orange"] "ack" == true
#guard findSubstring ["red", "black", "white", "green", "orange"] "abc" == false
#guard findSubstring ["red", "black", "white", "green", "orange"] "ange" == true
