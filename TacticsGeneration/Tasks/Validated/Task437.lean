import Batteries

open Std

def removeOdd (str1 : String) : String := Id.run do
  let n := str1.length
  let mut str2 := ""
  for i in [1 : n + 1] do
    if i % 2 == 0 then
      str2 := str2 ++ (str1.drop (i - 1)).take 1
  return str2

#guard removeOdd "python" = "yhn"
#guard removeOdd "program" = "rga"
#guard removeOdd "language" = "agae"
