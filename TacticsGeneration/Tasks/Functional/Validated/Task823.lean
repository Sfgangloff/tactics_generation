import Batteries

open Std

def containsSubstr (s sub : String) : Bool := Id.run do
  if sub.length == 0 then
    return true
  if s.length < sub.length then
    return false
  let limit := s.length - sub.length
  for i in [0 : limit + 1] do
    if (s.drop i).take sub.length == sub then
      return true
  return false

def check_substring (string sample : String) : String :=
  if containsSubstr string sample then
    let yStarts := (string.take sample.length) == sample
    if yStarts then
      "string starts with the given substring"
    else
      "string doesnt start with the given substring"
  else
    "entered string isnt a substring"

#guard check_substring "dreams for dreams makes life fun" "makes" = "string doesnt start with the given substring"
#guard check_substring "Hi there how are you Hi alex" "Hi" = "string starts with the given substring"
#guard check_substring "Its been a long day" "been" = "string doesnt start with the given substring"
