import Batteries

open Std

def string_length (str1 : String) : Nat :=
  str1.length

#guard string_length "python" == 6
#guard string_length "program" == 7
#guard string_length "language" == 8
