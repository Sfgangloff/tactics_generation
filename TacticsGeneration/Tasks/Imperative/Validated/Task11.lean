import Batteries



/-!
  Auto-generated from task 11.
  Module: Task11
-/

open Std

namespace Task11

/-- Remove first and last occurrence of a given character from the string.
    Preconditions: none. Works with Unicode characters; indices count characters. -/
def removeOcc (s : String) (ch : Char) : String := Id.run do
  let mut s := s
  -- Remove first occurrence
  let mut i := 0
  for c in s.data do
    if c == ch then
      s := (s.take i) ++ (s.drop (i + 1))
      break
    i := i + 1
  -- Remove last occurrence (scan forward and remember last index)
  let mut lastIdx : Nat := 0
  let mut found := false
  let mut j := 0
  for c in s.data do
    if c == ch then
      lastIdx := j
      found := true
    j := j + 1
  if found then
    s := (s.take lastIdx) ++ (s.drop (lastIdx + 1))
  return s

end Task11


-- Tests
open Std
open Task11

#eval (let r := removeOcc "hello" 'l'; if r == "heo" then () else panic! "assert 1 failed")
#eval (let r := removeOcc "abcda" 'a'; if r == "bcd" then () else panic! "assert 2 failed")
#eval (let r := removeOcc "PHP" 'P'; if r == "H" then () else panic! "assert 3 failed")
#eval (let r := removeOcc "hellolloll" 'l'; if r == "helollol" then () else panic! "assert 4 failed")
#eval (let r := removeOcc "" 'l'; if r == "" then () else panic! "assert 5 failed")
