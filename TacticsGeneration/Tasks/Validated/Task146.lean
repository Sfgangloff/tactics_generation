import Batteries

open Std

def ascii_value_string (str1 : String) : Nat :=
  
  match str1.toList with
  | c :: _ => Char.toNat c
  | [] => 0

#guard ascii_value_string "python" = 112
#guard ascii_value_string "Program" = 80
#guard ascii_value_string "Language" = 76
