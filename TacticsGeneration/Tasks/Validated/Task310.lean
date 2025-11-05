import Batteries

open Std

def string_to_tuple (str1 : String) : List Char :=
  str1.data.filter (fun x => !(Char.isWhitespace x))

#guard string_to_tuple "python 3.0" == ['p', 'y', 't', 'h', 'o', 'n', '3', '.', '0']
#guard string_to_tuple "item1" == ['i', 't', 'e', 'm', '1']
#guard string_to_tuple "15.10" == ['1', '5', '.', '1', '0']
