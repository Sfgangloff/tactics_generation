import Batteries

open Std

def isUpper (string : String) : String :=
  string.map Char.toUpper

#guard isUpper "person" == "PERSON"
#guard isUpper "final" == "FINAL"
#guard isUpper "Valid" == "VALID"
