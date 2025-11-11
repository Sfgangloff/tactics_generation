import Batteries

open Std

def findRotations (s : String) : Nat := Id.run do
  let n := s.length
  for k in [1 : n + 1] do
    if s == (s.drop k) ++ (s.take k) then
      return k
  return n

#guard findRotations "aaaa" == 1
#guard findRotations "ab" == 2
#guard findRotations "abc" == 3
