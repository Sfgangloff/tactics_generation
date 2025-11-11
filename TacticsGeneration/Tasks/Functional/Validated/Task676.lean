import Batteries

open Std

def isAsciiAlphaNum (c : Char) : Bool :=
  let n := c.toNat
  (n >= '0'.toNat && n <= '9'.toNat) ||
  (n >= 'A'.toNat && n <= 'Z'.toNat) ||
  (n >= 'a'.toNat && n <= 'z'.toNat)

def remove_extra_char (text1 : String) : String :=
  String.mk (text1.data.filter isAsciiAlphaNum)

#guard remove_extra_char "**//Google Android// - 12. " = "GoogleAndroid12"
#guard remove_extra_char "****//Google Flutter//*** - 36. " = "GoogleFlutter36"
#guard remove_extra_char "**//Google Firebase// - 478. " = "GoogleFirebase478"
