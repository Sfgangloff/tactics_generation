import Batteries

open Std

def oddValuesString (str : String) : String := Id.run do
  let n := str.length
  let mut result := ""
  for i in [0:n] do
    if i % 2 == 0 then
      result := result ++ (str.drop i).take 1
  return result

#guard oddValuesString "abcdef" == "ace"
#guard oddValuesString "python" == "pto"
#guard oddValuesString "data" == "dt"
