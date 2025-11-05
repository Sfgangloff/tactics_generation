import Batteries

open Std

def is_lower (string : String) : String :=
  string.foldl (fun (acc : String) (c : Char) => acc.push (Char.toLower c)) ""

#guard is_lower "InValid" = "invalid"
#guard is_lower "TruE" = "true"
#guard is_lower "SenTenCE" = "sentence"
