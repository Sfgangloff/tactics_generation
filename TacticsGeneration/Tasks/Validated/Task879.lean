import Batteries

open Std

def containsA (s : String) : Bool := Id.run do
  let n := s.length
  for i in [0 : n] do
    if (s.drop i).take 1 = "a" then
      return true
  return false

def text_match (text : String) : String :=
  let patterns := "a.*?b$"
  let len := text.length
  if len = 0 then "Not matched!"
  else
    let endsWithB := text.drop (len - 1) = "b"
    let hasA := containsA (text.take (len - 1))
    if endsWithB && hasA then "Found a match!" else "Not matched!"

#guard text_match "aabbbbd" == "Not matched!"
#guard text_match "aabAbbbc" == "Not matched!"
#guard text_match "accddbbjjjb" == "Found a match!"
