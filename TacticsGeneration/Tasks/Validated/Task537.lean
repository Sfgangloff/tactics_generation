import Batteries

open Std

def firstRepeatedWord (str1 : String) : String := Id.run do
  let words := str1.splitOn " "
  let mut temp : HashSet String := ({} : HashSet String)
  for word in words do
    if word ∈ temp then
      return word
    else
      temp := temp.insert word
  return "None"

#guard firstRepeatedWord "ab ca bc ab" == "ab"
#guard firstRepeatedWord "ab ca bc" == "None"
#guard firstRepeatedWord "ab ca bc ca ab bc" == "ca"
