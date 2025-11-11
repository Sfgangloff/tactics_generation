import Batteries

open Std

def textMatchString (text : String) : String :=
  let firstWord := text.takeWhile Char.isAlphanum
  if firstWord.length > 0 && text.drop firstWord.length != text then
    "Found a match!"
  else
    "Not matched!"

#guard textMatchString " python" == "Not matched!"
#guard textMatchString "python" == "Found a match!"
#guard textMatchString "  lang" == "Not matched!"
#guard textMatchString "foo" == "Found a match!"
