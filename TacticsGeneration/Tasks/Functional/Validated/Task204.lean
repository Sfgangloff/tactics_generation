import Batteries

open Std

def count (s : String) (c : String) : Nat := Id.run do
  let mut res := 0
  for i in [0 : s.length] do
    if (s.drop i).take 1 == c then
      res := res + 1
  return res

#guard count "abcc" "c" = 2
#guard count "ababca" "a" = 3
#guard count "mnmm0pm" "m" = 4
