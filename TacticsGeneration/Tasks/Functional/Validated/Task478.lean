import Batteries

open Std

def remove_lowercase (str1 : String) : String :=
  let isAsciiLower (c : Char) : Bool := c >= 'a' && c <= 'z'
  String.mk (str1.data.filter (fun c => !(isAsciiLower c)))

#guard remove_lowercase "PYTHon" == "PYTH"
#guard remove_lowercase "FInD" == "FID"
#guard remove_lowercase "STRinG" == "STRG"
