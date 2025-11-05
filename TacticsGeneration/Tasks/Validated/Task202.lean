import Batteries

open Std

def removeEven (str1 : String) : String := Id.run do
  let mut str2 := ""
  let mut i : Nat := 0
  for ch in str1.data do
    i := i + 1
    if i % 2 != 0 then
      str2 := str2.push ch
  return str2

#guard removeEven "python" == "pto"
#guard removeEven "program" == "porm"
#guard removeEven "language" == "lnug"
