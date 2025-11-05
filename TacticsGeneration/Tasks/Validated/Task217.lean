import Batteries

open Std

def first_Repeated_Char (str : String) : String := Id.run do
  let mut h : HashSet Char := {}
  for ch in str.toList do
    if h.contains ch then
      return String.singleton ch
    else
      h := h.insert ch
  return "\x00"

#guard first_Repeated_Char "Google" == "o"
#guard first_Repeated_Char "data" == "a"
#guard first_Repeated_Char "python" == "\x00"
