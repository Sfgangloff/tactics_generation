import Batteries

open Std

def containsSubstring (s p : String) : Bool := Id.run do
  let n := s.length
  let m := p.length
  if m == 0 then
    return true
  if m > n then
    return false
  for i in [0 : n - m + 1] do
    if (s.drop i).take m == p then
      return true
  return false

def check_literals (text : String) (patterns : List String) : String := Id.run do
  for pattern in patterns do
    if containsSubstring text pattern then
      return "Matched!"
    else
      return "Not Matched!"
  return "Not Matched!"

#guard check_literals "The quick brown fox jumps over the lazy dog." ["fox"] == "Matched!"
#guard check_literals "The quick brown fox jumps over the lazy dog." ["horse"] == "Not Matched!"
#guard check_literals "The quick brown fox jumps over the lazy dog." ["lazy"] == "Matched!"
