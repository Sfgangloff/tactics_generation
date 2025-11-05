import Batteries

open Std

def isWordPresent (sentence : String) (word : String) : Bool := Id.run do
  let s := sentence.splitOn " "
  for i in s do
    if i == word then
      return true
  return false

#guard isWordPresent "machine learning" "machine" == true
#guard isWordPresent "easy" "fun" == false
#guard isWordPresent "python language" "code" == false
