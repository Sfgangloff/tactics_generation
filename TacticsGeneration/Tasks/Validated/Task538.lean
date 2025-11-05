import Batteries

open Std

def string_list_to_tuple (str1 : String) : List Char :=
  str1.data.filter (fun c => !c.isWhitespace)

#guard string_list_to_tuple ("python 3.0") == ['p', 'y', 't', 'h', 'o', 'n', '3', '.', '0']
#guard string_list_to_tuple ("bigdata") == ['b', 'i', 'g', 'd', 'a', 't', 'a']
#guard string_list_to_tuple ("language") == ['l', 'a', 'n', 'g', 'u', 'a', 'g', 'e']
