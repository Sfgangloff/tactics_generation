import Batteries

open Std

def replaceChar (str1 : String) (ch : String) (newch : String) : String :=
  String.intercalate newch (str1.splitOn ch)

#guard replaceChar "polygon" "y" "l" == "pollgon"
#guard replaceChar "character" "c" "a" == "aharaater"
#guard replaceChar "python" "l" "a" == "python"
