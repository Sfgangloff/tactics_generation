import Batteries

open Std

def wordLen (s : String) : Bool :=
  let parts := s.splitOn " "
  let word := parts.headD ""
  if word.length % 2 = 0 then true else false

#guard wordLen "program" = false
#guard wordLen "solution" = true
#guard wordLen "data" = true
